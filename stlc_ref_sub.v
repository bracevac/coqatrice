Require Export Arith.EqNat.
Require Export Arith.Le.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Psatz. (* for lia *)
Import ListNotations.

(* Type soundness for lambda calculus with mutable references, recursive functions λf(x).t, and subtyping, quick and dirty.

   - Variables in locally nameless, deBruijn _levels_ for free vars.
   - Implements substitution in terms of opening.

   Nice to have: automation, automation, automation!
 *)

(* ### Syntax ### *)

Definition id := nat.
Definition loc := nat. (* store locations *)


(* locally nameless for binders in terms *)
Inductive var : Type :=
| varF : id -> var (* free var (deBruijn level) *)
| varB : id -> var (* locally-bound variable (deBruijn index) *)
.

Notation "# i" := (varB i) (at level 0).
Notation "$ i" := (varF i) (at level 0).

Inductive ty : Type :=
| TUnit : ty
| TFun  : ty -> ty -> ty
| TRef  : ty -> ty
.

Inductive tm : Type :=
| tunit    : tm
| tvar    : var -> tm
| tabs    : tm  -> tm (* convention: #0: self-ref #1: argument *)
| tapp    : tm  -> tm -> tm
| tloc    : loc -> tm
| tref    : tm  -> tm
| tderef  : tm  -> tm
| tassign : tm  -> tm -> tm
.

Notation "& l" := (tloc l) (at level 0).
Notation "! t" := (tderef t) (at level 0).
Coercion tvar : var >-> tm. (*lightens the notation of term variables*)

(* ### Representation of Bindings ### *)

(* An environment is a list of values, indexed by decrementing ids. *)

(* Look up a free variable (deBruijn level) in env   *)
Fixpoint indexr {X : Type} (n : id) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (beq_nat n (length l')) then Some a else indexr n l'
  end.

Lemma indexr_head : forall {A} {x : A} {xs}, indexr (length xs) (x :: xs) = Some x.
  intros. simpl. destruct (Nat.eqb (length xs) (length xs)) eqn:Heq. auto.
  apply beq_nat_false in Heq. contradiction.
Qed.

Lemma indexr_length : forall {A B} {xs : list A} {ys : list B}, length xs = length ys -> forall {x}, indexr x xs = None <-> indexr x ys = None.
Proof.
  intros A B xs.
  induction xs; intros; destruct ys; split; simpl in *; intros; eauto; try lia.
  - inversion H. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
  - inversion H. rewrite <- H2 in H0. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
Qed.

Lemma indexr_skip : forall {A} {x : A} {xs : list A} {i}, i <> length xs -> indexr i (x :: xs) = indexr i xs.
Proof.
  intros.
  rewrite <- PeanoNat.Nat.eqb_neq in H. auto.
  simpl. rewrite H. reflexivity.
Qed.

Lemma indexr_skips : forall {A} {xs' xs : list A} {i}, i < length xs -> indexr i (xs' ++ xs) = indexr i xs.
  induction xs'; intros; intuition.
  replace ((a :: xs') ++ xs) with (a :: (xs' ++ xs)).
  rewrite indexr_skip. eauto. rewrite app_length. lia. auto.
Qed.

Lemma indexr_var_some :  forall {A} {xs : list A} {i}, (exists x, indexr i xs = Some x) <-> i < length xs.
Proof.
  induction xs; intros; split; intros. inversion H. inversion H0.
  inversion H. inversion H. simpl in H0. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  apply beq_nat_true in Heq. rewrite Heq. auto. inversion H.
  simpl in H. rewrite Heq in H. apply IHxs in H. simpl. lia.
  simpl. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  exists a. reflexivity. apply beq_nat_false in Heq. simpl in H.
  apply IHxs. lia.
Qed.

(* easier to use for assumptions without existential quantifier *)
Lemma indexr_var_some' :  forall {A} {xs : list A} {i x}, indexr i xs = Some x -> i < length xs.
Proof.
  intros. apply indexr_var_some. exists x. auto.
Qed.

Lemma indexr_var_none :  forall {A} {xs : list A} {i}, indexr i xs = None <-> i >= length xs.
Proof.
  induction xs; intros; split; intros.
  simpl in *. lia. auto.
  simpl in H.
  destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  discriminate. apply IHxs in H. apply beq_nat_false in Heq. simpl. lia.
  assert (Hleq: i >= length xs). {
    simpl in H. lia.
  }
  apply IHxs in Hleq. rewrite <- Hleq.
  apply indexr_skip. simpl in H. lia.
Qed.

Lemma indexr_insert_ge : forall {A} {xs xs' : list A} {x} {y}, x >= (length xs') -> indexr x (xs ++ xs') = indexr (S x) (xs ++ y :: xs').
  induction xs; intros.
  - repeat rewrite app_nil_l. pose (H' := H).
    rewrite <- indexr_var_none in H'.
    rewrite H'. symmetry. apply indexr_var_none. simpl. lia.
  - replace ((a :: xs) ++ xs') with (a :: (xs ++ xs')); auto.
    replace ((a :: xs) ++ y :: xs') with (a :: (xs ++ y :: xs')); auto.
    simpl. replace (length (xs ++ y :: xs')) with (S (length (xs ++ xs'))).
    destruct (Nat.eqb x (length (xs ++ xs'))) eqn:Heq; auto.
    repeat rewrite app_length. simpl. lia.
Qed.

Lemma indexr_insert_lt : forall {A} {xs xs' : list A} {x} {y}, x < (length xs') -> indexr x (xs ++ xs') = indexr x (xs ++ y :: xs').
  intros.
  rewrite indexr_skips; auto.
  erewrite indexr_skips.
  erewrite indexr_skip. auto.
  lia. simpl. lia.
Qed.

Lemma indexr_insert:  forall {A} {xs xs' : list A} {y}, indexr (length xs') (xs ++ y :: xs') = Some y.
  intros. induction xs.
  - replace ([] ++ y :: xs') with (y :: xs'); auto. apply indexr_head.
  - simpl. rewrite IHxs. rewrite app_length. simpl.
    destruct (PeanoNat.Nat.eqb (length xs') (length xs + S (length xs'))) eqn:Heq; auto.
    apply beq_nat_true in Heq. lia.
Qed.

Definition tenv := list ty. (* Γ environment: static *)
Definition senv := list ty. (* Sigma store typing *)

Definition extends {A} (l1 l2 : list A): Prop := exists l', l1 = l' ++ l2.
Notation "x ⊇ y" := (extends x y) (at level 0).

Lemma extends_refl : forall {A}, forall{l : list A}, extends l l.
  intros. unfold extends. exists []. auto.
Qed.

Lemma extends_cons : forall {A}, forall{l : list A}, forall{a:A}, extends (a :: l) l.
  intros. unfold extends. exists [a]. auto.
Qed.

Lemma extends_length : forall {A}, forall{l1 l2 : list A}, extends l1 l2 -> length l1 >= length l2.
  intros. unfold extends in H. destruct H as [l' Heq]. subst. rewrite app_length. lia.
Qed.

(* Opening a term *)
Fixpoint open_rec_tm (k : nat) (u : tm) (t : tm) {struct t} : tm :=
  match t with
  | tunit            => tunit
  | tvar   (varF x) => tvar (varF x)
  | tvar   (varB x) => if beq_nat k x then u else tvar (varB x)
  | tabs    t       => tabs    (open_rec_tm (S (S k)) u t)
  | tapp    t1 t2   => tapp    (open_rec_tm k u t1) (open_rec_tm k u t2)
  | tloc    l       => tloc l
  | tref    t       => tref    (open_rec_tm k u t)
  | tderef  t       => tderef  (open_rec_tm k u t)
  | tassign t1 t2   => tassign (open_rec_tm k u t1) (open_rec_tm k u t2)
  end
.
(*simultaneous opening with self-ref and argument: *)
Definition open_tm (u u' : tm) t := open_rec_tm 1 u' (open_rec_tm 0 u t).
Definition open_tm' {A : Type} (env : list A) t :=
  open_rec_tm 1 (varF (S (length env))) (open_rec_tm 0 (varF (length env)) t).

Lemma open_rec_tm_commute : forall t i j x y, i <> j -> open_rec_tm i (varF x) (open_rec_tm j (varF y) t) = open_rec_tm j (varF y) (open_rec_tm i (varF x) t).
  induction t; intros; simpl; eauto;
    try solve [rewrite IHt1; eauto; rewrite IHt2; eauto | rewrite IHt; eauto].
  destruct v. intuition.
  destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
    try rewrite Hii0; try rewrite Hji0; auto.
  apply beq_nat_true in Hii0. apply beq_nat_true in Hji0. subst. contradiction.
Qed.

(* measure for induction over terms *)
Fixpoint tm_size (t : tm) : nat :=
  match t with
  | tunit          => 0
  | tvar    _     => 0
  | tabs    t     => S (tm_size t)
  | tapp    t1 t2 => S (tm_size t1 + tm_size t2)
  | tloc    _     => 0
  | tref    t     => S (tm_size t)
  | tderef  t     => S (tm_size t)
  | tassign t1 t2 => S (tm_size t1 + tm_size t2)
  end.

Lemma open_preserves_size: forall t x j, tm_size t = tm_size (open_rec_tm j (tvar x) t).
  induction t; intros; simpl; eauto.
  destruct v. auto. destruct (Nat.eqb j i); auto.
Qed.

Inductive closed_tm: nat(*B*) -> nat(*F*) -> nat(*Loc*) -> tm -> Prop :=
| cl_tsct : forall b f l,
    closed_tm b f l tunit
| cl_tvarb: forall b f l x,
    x < b ->
    closed_tm b f l (tvar (varB x))
| cl_tvarf: forall b f l x,
    x < f ->
    closed_tm b f l (tvar (varF x))
| cl_tabs:  forall b f l tm,
    closed_tm (S (S b)) f l tm ->
    closed_tm b f l (tabs tm)
| cl_tapp:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tapp tm1 tm2)
| cl_tloc: forall b f l l',
    l' < l ->
    closed_tm b f l (tloc l')
| cl_tref:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tref tm)
| cl_tderef:  forall b f l tm,
    closed_tm b f l tm ->
    closed_tm b f l (tderef tm)
| cl_tassign:  forall b f l tm1 tm2,
    closed_tm b f l tm1 ->
    closed_tm b f l tm2 ->
    closed_tm b f l (tassign tm1 tm2)
.
Hint Constructors closed_tm : dsub.

Inductive stp : tenv -> senv -> ty -> ty -> Prop :=
| s_base : forall Γ Σ,
    stp Γ Σ TUnit TUnit
| s_ref : forall Γ Σ T, (* TODO: generalize to equivalence*)
    stp Γ Σ (TRef T) (TRef T)
| s_fun : forall Γ Σ T1 T3 T2 T4,  (*TODO: this becomes less trivial with the qualifiers *)
    stp Γ Σ T3 T1 ->
    stp Γ Σ T2 T4 ->
    stp Γ Σ (TFun T1 T2) (TFun T3 T4)
.

Inductive has_type : tenv -> senv -> tm -> ty -> Prop :=
| t_base : forall Γ Σ,
    has_type Γ Σ tunit TUnit

| t_var : forall Γ Σ x T,
    indexr x Γ = Some T ->
    has_type Γ Σ (tvar (varF x)) T

| t_abs: forall Γ Σ T1 T2 t,
    closed_tm 2 (length Γ) (length Σ) t ->
    has_type (T1 :: (TFun T1 T2) :: Γ) Σ (open_tm' Γ t) T2 ->
    has_type Γ Σ (tabs t) (TFun T1 T2)

| t_app : forall Γ Σ t1 t2 T1 T2,
    has_type Γ Σ t1 (TFun T1 T2) ->
    has_type Γ Σ t2 T1 ->
    has_type Γ Σ (tapp t1 t2) T2

| t_loc : forall Γ Σ l T,
    indexr l Σ = Some T ->
    has_type Γ Σ (tloc l) (TRef T)

| t_ref: forall Γ Σ T t,
    has_type Γ Σ t T ->
    has_type Γ Σ (tref t) (TRef T)

| t_deref: forall Γ Σ T t,
    has_type Γ Σ t (TRef T) ->
    has_type Γ Σ (tderef t) T

| t_assign: forall Γ Σ T t1 t2,
    has_type Γ Σ t1 (TRef T) ->
    has_type Γ Σ t2 T ->
    has_type Γ Σ (tassign t1 t2) TUnit

| t_sub: forall Γ Σ e T1 T2,
    has_type Γ Σ e T1 ->
    stp Γ Σ T1 T2 ->
    has_type Γ Σ e T2
.

Hint Constructors has_type : dsub.
Hint Constructors stp : dsub.

Lemma bound_vars_untypable : forall {Γ Σ T i}, has_type Γ Σ #i T -> False.
  intros Γ Σ T i HT. remember (tvar #i) as t. induction HT; try discriminate.
  intuition.
Qed.

Lemma closed_tm_monotone : forall {t b l f}, closed_tm b f l t -> forall {b' f' l'}, b <= b' -> f <= f' -> l <= l' -> closed_tm b' f' l' t.
  intros T b f l H. induction H; intuition.
Qed.

Lemma closed_tm_open_id : forall {t b f l}, closed_tm b f l t -> forall {n}, b <= n -> forall {x}, (open_rec_tm n x t) = t.
  intros t b f l H. induction H; intros; simpl; auto;
    try solve [erewrite IHclosed_tm1; eauto; erewrite IHclosed_tm2; eauto; lia | erewrite IHclosed_tm; eauto; lia].
  destruct (Nat.eqb n x) eqn:Heq; auto. apply beq_nat_true in Heq. lia.
Qed.

Lemma closed_tm_open : forall {T b f l}, closed_tm (S b) f l T -> forall {x}, x < f -> closed_tm b f l (open_rec_tm b (varF x) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [apply IHT1; auto | apply IHT2; auto | apply IHT; auto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition.
  apply beq_nat_false in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_tm_open' : forall {T b f l}, closed_tm (S b) f l T -> forall {x}, x <= f -> forall {t}, closed_tm 0 x l t -> closed_tm b f l (open_rec_tm b t T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
  try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq; intuition. eapply closed_tm_monotone; eauto; lia.
  apply beq_nat_false in Heq. constructor. lia. auto. auto.
Qed.

Lemma closed_tm_open_ge : forall {T b f l}, closed_tm (S b) f l T -> forall {x}, f <= x -> closed_tm b (S x) l (open_rec_tm b (varF x) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
      try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
  destruct (Nat.eqb b x0) eqn:Heq. intuition.
  apply beq_nat_false in Heq. inversion H. subst.
  constructor. lia. lia. auto.
Qed.

Lemma closed_open_succ : forall {T b f l}, closed_tm b f l T -> forall {j}, closed_tm b (S f) l (open_rec_tm j (varF f) T).
  induction T; intros; simpl; intuition; inversion H; subst; try constructor;
    try solve [eapply IHT1; eauto | eapply IHT2; eauto | eapply IHT; eauto ].
    destruct (Nat.eqb j x) eqn:Heq. intuition.
    apply beq_nat_false in Heq. inversion H. subst. intuition. lia. auto.
Qed.

Lemma open_rec_tm_commute' : forall t i j x t' f l, i <> j -> closed_tm 0 f l t' -> open_rec_tm i (varF x) (open_rec_tm j t' t) = open_rec_tm j t' (open_rec_tm i (varF x) t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  - destruct v. intuition.
    destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply beq_nat_true in Hii0. apply beq_nat_true in Hji0. subst. contradiction.
    eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma open_rec_tm_commute'' : forall t i j t' t'' f l, i <> j -> closed_tm 0 f l t' -> closed_tm 0 f l t'' -> open_rec_tm i t'' (open_rec_tm j t' t) = open_rec_tm j t' (open_rec_tm i t'' t).
  induction t; intros; simpl; eauto;
    try solve [erewrite IHt1; eauto; erewrite IHt2; eauto | erewrite IHt; eauto].
  - destruct v. intuition.
    destruct (Nat.eqb i i0) eqn:Hii0; destruct (Nat.eqb j i0) eqn:Hji0; simpl;
      try rewrite Hii0; try rewrite Hji0; auto.
    apply beq_nat_true in Hii0. apply beq_nat_true in Hji0. subst. contradiction.
    symmetry. eapply closed_tm_open_id; eauto. lia. eapply closed_tm_open_id; eauto. lia.
Qed.

Lemma has_type_var_length : forall {Γ Σ x T}, has_type Γ Σ (tvar (varF x)) T -> x < length Γ.
  intros. dependent induction H; eauto.
  apply indexr_var_some' in H. auto.
Qed.

Fixpoint has_type_closed  {Γ Σ t T} (ht  : has_type Γ Σ t T) : closed_tm 0 (length Γ) (length Σ) t.

  destruct ht; intuition; try apply has_type_closed in ht; try apply has_type_closed in ht1;
    try apply has_type_closed in ht2; intuition.
  + apply indexr_var_some' in H. intuition.
  + apply indexr_var_some' in H. intuition.
Qed.

Require Import Coq.Arith.Compare_dec.

Fixpoint splice (n : nat) (t : tm) {struct t} : tm :=
  match t with
  | tunit           => tunit
  | tvar (varF i)  =>
    if le_lt_dec n i then tvar (varF (S i))
    else tvar (varF i)
  | tvar (varB i)  => tvar    (varB i)
  | tabs    t      => tabs    (splice n t)
  | tapp    t1 t2  => tapp    (splice n t1) (splice n t2)
  | tloc    l      => tloc     l
  | tref    t      => tref    (splice n t)
  | tderef  t      => tderef  (splice n t)
  | tassign t1 t2  => tassign (splice n t1) (splice n t2)
  end.

Lemma splice_id : forall {T b f l}, closed_tm b f l T -> (splice f T ) = T.
  induction T; intros; inversion H; subst; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
    destruct (le_lt_dec f x) eqn:Heq. lia. auto.
Qed.

Lemma splice_open : forall {T j n m}, splice n (open_rec_tm j (varF (m + n)) T) = open_rec_tm j (varF (S (m + n))) (splice n T).
  induction T; intros; simpl; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct v; simpl. destruct (le_lt_dec n i) eqn:Heq; auto.
  destruct (PeanoNat.Nat.eqb j i) eqn:Heq; auto.
  simpl. destruct (le_lt_dec n (m + n)) eqn:Heq'. auto. lia.
Qed.

Lemma splice_open' :  forall {T} {A} {D : A} {ρ ρ'}, splice (length ρ') (open_tm' (ρ ++ ρ') T) = open_tm' (ρ ++ D :: ρ') (splice (length ρ') T).
  intros. unfold open_tm'.
  replace (length (ρ ++ ρ')) with ((length ρ) + (length ρ')).
  replace (S (length (ρ ++ D :: ρ'))) with (S (S (length ρ) + (length ρ'))).
  replace (length (ρ ++ D :: ρ')) with (S ((length ρ) + (length ρ'))).
  rewrite <- splice_open.
  rewrite <- splice_open.
  reflexivity.
  all: rewrite app_length; simpl; lia.
Qed.

Lemma splice_closed : forall {T b n m l}, closed_tm b (n + m) l T -> closed_tm b (S (n + m)) l (splice m T).
  induction T; simpl; intros; inversion H; subst; intuition.
  destruct (le_lt_dec m x) eqn:Heq; intuition.
Qed.

Lemma splice_closed' : forall {T b l} {A} {D : A} {ρ ρ'},
    closed_tm b (length (ρ ++ ρ')) l T ->  closed_tm b (length (ρ ++ D :: ρ')) l (splice (length ρ') T).
  intros. rewrite app_length in H.
  replace (length (ρ ++ D :: ρ')) with (S (length ρ) + (length ρ')).
  apply splice_closed. auto. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma splice_open_succ : forall {T b n l j}, closed_tm b n l T -> splice n (open_rec_tm j (varF n) T) = open_rec_tm j (varF (S n)) T.
  induction T; simpl; intros; inversion H; subst; auto;
    try solve [erewrite IHT1; eauto; erewrite IHT2; eauto | erewrite IHT; eauto].
  destruct (PeanoNat.Nat.eqb j x) eqn:Heq; auto. simpl.
  destruct (le_lt_dec n n) eqn:Heq'; auto. lia.
  simpl. destruct (le_lt_dec n x) eqn:Heq; auto. lia.
Qed.

Inductive value : tm -> Prop :=
| value_abs : forall t, value (tabs t)
| value_cst : value tunit
| value_loc : forall l, value (tloc l)
.

Definition store := list tm.

Fixpoint update (σ : store) (l : loc) (v : tm) : store :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (beq_nat l (length σ')) then (v :: σ') else (a :: (update σ' l v ))
  end.

Lemma update_length : forall {σ l v}, length σ = length (update σ l v).
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Heq; intuition.
  simpl. congruence.
Qed.

Lemma update_indexr_miss : forall {σ l v l'}, l <> l' ->  indexr l' (update σ l v) = indexr l' σ.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls; destruct (Nat.eqb l' (length σ)) eqn:Hl's.
  apply beq_nat_true in Hls. apply beq_nat_true in Hl's. rewrite <- Hl's in Hls. contradiction.
  simpl. rewrite Hl's. auto.
  simpl. rewrite <- update_length. rewrite Hl's. auto.
  simpl. rewrite <- update_length. rewrite Hl's. apply IHσ. auto.
Qed.

Lemma update_indexr_hit : forall {σ l v}, l < length σ -> indexr l (update σ l v) = Some v.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls.
  apply beq_nat_true in Hls. rewrite Hls. apply indexr_head.
  simpl. rewrite <- update_length. rewrite Hls. apply beq_nat_false in Hls.
  apply IHσ. lia.
Qed.

Inductive step : tm -> store -> tm -> store -> Prop :=
(*contraction rules*)
| step_beta : forall t v σ,
    value v ->
    step (tapp (tabs t) v) σ (open_tm (tabs t) v t) σ
| step_ref : forall v σ,
    value v ->
    step (tref v) σ (tloc (length σ)) (v :: σ)
| step_deref : forall σ l v,
    indexr l σ = Some v ->
    value v ->
    step (tderef (tloc l)) σ v σ
| step_assign : forall σ l v,
    l < (length σ) ->
    value v ->
    step (tassign (tloc l) v) σ tunit (update σ l v)
(*congruence rules*)
| step_c_ref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tref t) σ (tref t') σ'
| step_c_deref : forall t t' σ σ',
    step t σ t' σ' ->
    step (tderef t) σ (tderef t') σ'
| step_c_app_l : forall t1 t1' t2 σ σ',
    step t1 σ t1' σ' ->
    step (tapp t1 t2) σ (tapp t1' t2) σ'
| step_c_app_r : forall v t2 t2' σ σ',
    value v ->
    step t2 σ t2' σ' ->
    step (tapp v t2) σ (tapp v t2') σ'
| step_c_assign_l : forall t1 t1' t2 σ σ',
    step t1 σ t1' σ' ->
    step (tassign t1 t2) σ (tassign t1' t2) σ'
| step_c_assign_r : forall v t2 t2' σ σ',
    value v ->
    step t2 σ t2' σ' ->
    step (tassign v t2) σ (tassign v t2') σ'
.

Lemma values_stuck : forall {v}, value v -> forall {t σ σ'}, step v σ t σ' -> False.
  intros. inversion H0; subst; inversion H.
Qed.

Lemma stp_refl : forall {T Γ Σ}, stp Γ Σ T T.
  induction T; intros; intuition.
Qed.

Lemma stp_trans : forall {T2 T1 T3 Γ Σ}, stp Γ Σ T1 T2 -> stp Γ Σ T2 T3 -> stp Γ Σ T1 T3.
  induction T2; intros; try inversion H0; try inversion H; intuition.
Qed.

(* Inversion lemmas abstracting over subsumption steps *)
Lemma typ_inv_unit : forall {Γ Σ T}, has_type Γ Σ tunit T -> T = TUnit.
  intros Γ Σ T HT. remember tunit as t. induction HT; try solve [discriminate].
  auto. intuition. subst. inversion H. subst. auto.
Qed.

Lemma typ_inv_varf : forall {Γ Σ i T}, has_type Γ Σ $i T -> exists U, indexr i Γ = Some U /\ stp Γ Σ U T.
  intros Γ Σ i T HT. remember (tvar $i) as v. induction HT; inversion Heqv; subst.
  - exists T. intuition. apply stp_refl.
  - intuition. destruct H1 as [U [Hlookup UsubT1]].
    exists U. intuition. eapply stp_trans; eauto.
Qed.

Lemma typ_inv_loc : forall {Γ Σ l T}, has_type Γ Σ &l T -> exists U, indexr l Σ = Some U /\ stp Γ Σ (TRef U) T.
  intros Γ Σ l T HT. remember &l as v. induction HT; inversion Heqv; subst.
  - exists T. intuition.
  - intuition. destruct H1 as [U [Hlookup UsubT1]].
    exists U. intuition. eapply stp_trans; eauto.
Qed.

Lemma typ_inv_ref : forall {Γ Σ t T}, has_type Γ Σ (tref t) T -> exists U, T = TRef U /\ has_type Γ Σ t U.
  intros Γ Σ t T HT. remember (tref t) as ref. induction HT; inversion Heqref; subst.
  - exists T. intuition.
  - intuition. destruct H1 as [U [HRef Ht]]. subst.
    inversion H. subst. exists U. intuition.
Qed.

Lemma typ_inv_deref : forall {Γ Σ t T}, has_type Γ Σ !t T -> exists U, has_type Γ Σ t (TRef U) /\ stp Γ Σ U T.
  intros Γ Σ t T HT. remember !t as ref. induction HT; inversion Heqref; subst.
  - exists T. intuition. apply stp_refl.
  - intuition. destruct H1 as [U [Ht Hstp]].
    exists U. intuition. eapply stp_trans; eauto.
Qed.

Lemma typ_inv_abs : forall {Γ Σ t T},
    has_type Γ Σ (tabs t) T ->
    exists T1 T2, closed_tm 2 (length Γ) (length Σ) t /\ has_type (T1 :: (TFun T1 T2) :: Γ) Σ (open_tm' Γ t) T2 /\ stp Γ Σ (TFun T1 T2) T.
  intros Γ Σ t T HT. remember (tabs t) as abs. induction HT; inversion Heqabs; subst.
  - exists T1. exists T2. intuition. apply stp_refl.
  - intuition. destruct H1 as [T1' [T2' [Hc [Ht Hstp]]]]. exists T1'. exists T2'.
    intuition. inversion Hstp. subst. inversion H. subst. eapply stp_trans; eauto.
Qed.

Lemma typ_inv_app : forall {Γ Σ t1 t2 T},
    has_type Γ Σ (tapp t1 t2) T ->
    exists T1, has_type Γ Σ t1 (TFun T1 T) /\ has_type Γ Σ t2 T1.
  intros Γ Σ t1 t2 T HT. remember (tapp t1 t2) as app. induction HT; inversion Heqapp; subst.
  - exists T1. intuition.
  - intuition. destruct H1 as [T' [Ht1 Ht2]].
    exists T'. split. eapply t_sub. eauto. constructor. apply stp_refl. auto.
    auto.
Qed.

Lemma typ_inv_assign : forall {Γ Σ t1 t2 T},
    has_type Γ Σ (tassign t1 t2) T -> T = TUnit /\ exists U, has_type Γ Σ t1 (TRef U) /\ has_type Γ Σ t2 U.
  intros Γ Σ t1 t2 T HT. remember (tassign t1 t2) as ass. induction HT; inversion Heqass; subst.
  - intuition. exists T. intuition.
  - intuition. subst. inversion H. subst. auto.
Qed.

Lemma weaken_stp_gen : forall {Γ1 Γ2 Σ T1 T2},
    stp (Γ1 ++ Γ2) Σ T1 T2 ->
    forall T', stp (Γ1 ++ T' :: Γ2) Σ T1 T2.
  intros Γ1 Γ2 Σ T1 T2 Hstp. induction Hstp; intuition.
Qed.

Lemma weaken_stp : forall {Γ Σ T1 T2}, stp Γ Σ T1 T2 -> forall T', stp (T' :: Γ) Σ T1 T2.
  intros. specialize (@weaken_stp_gen [] Γ Σ T1 T2) as Hsp.
  simpl in *. intuition.
Qed.

Lemma weaken_stp' : forall {Γ Σ T1 T2}, stp Γ Σ T1 T2 -> forall Γ', stp (Γ' ++ Γ) Σ T1 T2.
  intros. induction Γ'.
  - simpl. auto.
  - replace ((a :: Γ') ++ Γ) with (a :: (Γ' ++ Γ)).
    apply weaken_stp. auto. simpl. auto.
Qed.

Lemma weaken_gen : forall {n t Γ1 Γ2 Σ T}, tm_size t < n ->
    closed_tm 0 (length (Γ1 ++ Γ2)) (length Σ) t ->
    has_type (Γ1 ++ Γ2) Σ t T ->
    forall T', has_type (Γ1 ++ T' :: Γ2) Σ (splice (length Γ2) t) T.
  induction n; try lia; intros; destruct t; simpl.
  - apply typ_inv_unit in H1. subst. constructor.
  - destruct v; inversion H0; subst; try lia.
    apply typ_inv_varf in H1. destruct H1 as [U [Hlookup Hstp]].
    destruct (le_lt_dec (length Γ2) i) eqn:Heq.
    rewrite (@indexr_insert_ge _ Γ1 Γ2 i T' l) in Hlookup.
    2 : rewrite (@indexr_insert_lt _ Γ1 Γ2 i T' l) in Hlookup.
    all: eapply t_sub.
    1,3: constructor; apply Hlookup.
    all: apply weaken_stp_gen; auto.
  - (*tabs*) simpl in H. inversion H0; subst.
    apply typ_inv_abs in H1. destruct H1 as [T1 [T2 [Hc [Ht Hstp]]]].
    inversion Hstp. subst. eapply t_sub. apply t_abs.
    3: apply weaken_stp_gen; eapply Hstp.
    apply splice_closed'. auto.
    rewrite <- splice_open'.
    replace (T1 :: TFun T1 T2 :: Γ1 ++ T' :: Γ2) with ((T1 :: TFun T1 T2 :: Γ1) ++ T' :: Γ2).
    eapply IHn; eauto. unfold open_tm'. rewrite <- open_preserves_size. rewrite <- open_preserves_size. lia.
    simpl. eapply closed_tm_monotone. eapply has_type_closed; eauto. lia. simpl. lia. auto.
    intuition.
  - simpl in H. inversion H0; subst. apply typ_inv_app in H1.
    destruct H1 as [U [Ht1 Ht2]]. eapply t_app.
    eapply IHn; eauto. lia. eapply IHn; eauto. lia.
  - apply typ_inv_loc in H1. destruct H1 as [U [Hlookup Hstp]].
    eapply t_sub. apply t_loc. eauto. apply weaken_stp_gen. auto.
  - simpl in H. apply typ_inv_ref in H1. destruct H1 as [U [Heq Ht]].
    subst. inversion H0. subst. apply t_ref. eapply IHn; eauto. lia.
  - simpl in H. inversion H0; subst. apply typ_inv_deref in H1.
    destruct H1 as [U [Ht Hstp]]. eapply t_sub. apply t_deref. eapply IHn; eauto. lia.
    apply weaken_stp_gen. auto.
  - simpl in H. inversion H0; subst. apply typ_inv_assign in H1.
    destruct H1 as [Heq [U [Ht1 Ht2]]]. subst.
    eapply t_assign. eapply IHn; eauto; lia. eapply IHn; eauto; lia.
Qed.

Lemma weaken : forall {Γ Σ t T}, has_type Γ Σ t T -> forall {T'}, has_type (T' :: Γ) Σ t T.
  intros Γ Σ t T HT. specialize (@weaken_gen (S (tm_size t)) t [] Γ Σ T) as Hsp. simpl in *.
  replace (splice (length Γ) t) with t in Hsp.
  apply Hsp; auto. eapply has_type_closed; eauto.
  symmetry. eapply splice_id. eapply has_type_closed; eauto.
Qed.

Lemma weaken' : forall {Γ Σ t T}, has_type Γ Σ t T -> forall {Γ'}, has_type (Γ' ++ Γ) Σ t T.
  intros. induction Γ'.
  - simpl. auto.
  - replace ((a :: Γ') ++ Γ) with (a :: (Γ' ++ Γ)).
    apply weaken. auto. simpl. auto.
Qed.

Lemma weaken_stp_store : forall {Γ Σ T1 T2}, stp Γ Σ T1 T2 -> forall {Σ'}, Σ' ⊇ Σ -> stp Γ Σ' T1 T2.
  intros Γ Σ T1 T2 HST. induction HST; intuition.
Qed.

Lemma weaken_store : forall {Γ Σ t T}, has_type Γ Σ t T -> forall {Σ'}, Σ' ⊇ Σ -> has_type Γ Σ' t T.
  intros Γ Σ t T HT. induction HT; intros; intuition.
  - apply t_abs. eapply closed_tm_monotone; eauto. apply extends_length. auto.
    apply IHHT. auto.
  - eapply t_app. eapply IHHT1; auto. eapply IHHT2; auto.
  - eapply t_loc. unfold extends in H0. destruct H0. rewrite H0.
    rewrite indexr_skips. auto. eapply indexr_var_some'. eauto.
  - eapply t_assign. eapply IHHT1; auto. eapply IHHT2; auto.
  - eapply t_sub; eauto. eapply weaken_stp_store; eauto.
Qed.

(* canonical forms *)
Lemma canonical_unit : forall {Σ t}, has_type [] Σ t TUnit -> value t -> t = tunit.
  intros. remember [] as Γ. remember TUnit as T. induction H; intuition; try discriminate;
                                                   inversion H0; subst; auto.
  all: inversion H1; subst; intuition.
Qed.

Lemma canonical_fun : forall {Σ t T1 T2}, has_type [] Σ t (TFun T1 T2) -> value t -> exists t', t = (tabs t').
  intros. remember [] as Γ. remember (TFun T1 T2) as T. induction H; intuition; try discriminate;
                                                          inversion H0; subst.
  - exists t. auto.
  - exists t. auto.
  - apply typ_inv_unit in H. subst. inversion H1.
  - apply typ_inv_loc in H. repeat destruct H. inversion H3. subst. inversion H1.
Qed.

Lemma canonical_ref : forall {Σ t T}, has_type [] Σ t (TRef T) -> value t -> exists l, t = &l.
  intros. remember [] as Γ. remember (TRef T) as R. induction H; intuition; try discriminate;
                                                          inversion H0; subst.
  - exists l. auto.
  - apply typ_inv_abs in H. destruct H as [T2 [T3 [Hc [Ht Hstp]]]].
    inversion Hstp. subst. inversion H1.
  - apply typ_inv_unit in H. subst. inversion H1.
  - exists l. auto.
Qed.

Lemma narrowing_stp_gen : forall{Γ1 U Γ2 Σ T1 T2}, stp (Γ1 ++ U :: Γ2) Σ T1 T2 -> forall {V}, stp Γ2 Σ V U -> stp (Γ1 ++ V :: Γ2) Σ T1 T2.
  intros Γ1 U Γ2 Σ T1 T2 HST. remember (Γ1 ++ U :: Γ2) as Γ. generalize dependent Γ1; induction HST; intros; subst; intuition.
Qed.

Lemma narrowing_stp : forall{Γ U Σ T1 T2}, stp (U :: Γ) Σ T1 T2 -> forall {V}, stp Γ Σ V U -> stp (V :: Γ) Σ T1 T2.
  intros. specialize (@narrowing_stp_gen [] U Γ Σ T1 T2) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma narrowing_gen : forall{Γ1 U Γ2 Σ t T}, has_type (Γ1 ++ U :: Γ2) Σ t T -> forall {V}, stp Γ2 Σ V U -> has_type (Γ1 ++ V :: Γ2) Σ t T.
  intros Γ1 U Γ2 Σ t T HT. remember (Γ1 ++ U :: Γ2) as Γ. generalize dependent Γ1; induction HT; intros; subst; intuition.
  - destruct (PeanoNat.Nat.lt_trichotomy x (length Γ2)) as [Hlen | [Hlen | Hlen] ].
    + apply t_var. rewrite <- (indexr_insert_lt Hlen). rewrite <- (indexr_insert_lt Hlen) in H. auto.
    + rewrite Hlen in *. rewrite indexr_insert in H. inversion H. subst.
      apply (t_sub _ _ $(length Γ2) V T). apply t_var. rewrite indexr_insert. auto. eapply weaken_stp_gen.
      apply weaken_stp'. auto.
    + inversion Hlen. apply t_var. rewrite <- indexr_insert_ge; eauto. rewrite <- H1 in H.
      rewrite <- indexr_insert_ge in H; eauto. rewrite <- H2 in H.
      apply t_var. rewrite <- indexr_insert_ge; eauto. rewrite <- indexr_insert_ge in H; eauto. lia. lia.
  - apply t_abs. replace (length (Γ1 ++ V :: Γ2)) with (length (Γ1 ++ U :: Γ2)). auto.
    repeat rewrite app_length. simpl. auto.
    replace (T1 :: TFun T1 T2 :: Γ1 ++ V :: Γ2) with ((T1 :: TFun T1 T2 :: Γ1) ++ V :: Γ2); intuition.
    replace (open_tm' (Γ1 ++ V :: Γ2) t) with (open_tm' (Γ1 ++ U :: Γ2) t); eauto.
    unfold open_tm'. repeat rewrite app_length. simpl. auto.
  - eapply t_app. eapply IHHT1; eauto. eapply IHHT2; eauto.
  - eapply t_assign. eapply IHHT1; eauto. eapply IHHT2; eauto.
  - eapply t_sub; eauto. eapply narrowing_stp_gen; eauto.
Qed.

Lemma narrowing : forall{Γ U Σ t T}, has_type (U :: Γ) Σ t T -> forall {V}, stp Γ Σ V U -> has_type (V :: Γ) Σ t T.
  intros. specialize (@narrowing_gen [] U Γ Σ t T) as narrow. simpl in *. eapply narrow; eauto.
Qed.

Lemma strengthen_stp : forall {Γ1 T1 Γ2 Σ T2 T3}, stp (Γ1 ++ T1 :: Γ2) Σ T2 T3 -> stp (Γ1 ++ Γ2) Σ T2 T3.
  intros Γ1 T1 Γ2 Σ T2 T3 HST. induction HST; intuition.
Qed.

(* This pops up in the general substitution lemma when we deal with lambdas. *)
Lemma substitution_closed :  forall {k t b m n l i j}, tm_size t < k -> i <> j ->
    closed_tm (S (S b)) (m + S (S n)) l (open_rec_tm (S (S j)) $(S n) (open_rec_tm (S (S i)) $n (splice (S n) (splice n t)))) ->
    forall {tx tf}, closed_tm 0 n l tx -> closed_tm 0 n l tf ->
               closed_tm (S (S b)) (m + n) l (open_rec_tm (S (S j)) tx (open_rec_tm (S (S i)) tf t)).
  induction k; try lia; destruct t; intros; simpl in *; try solve [inversion H1; subst; constructor; auto; eapply IHk; eauto; lia].
  destruct v. simpl in *. constructor. destruct (le_lt_dec n i0) eqn:Hlt.
  replace (splice (S n) $(S i0)) with (tvar $(S (S i0))) in H1.
  simpl in *. inversion H1. subst. lia. unfold splice. destruct (le_lt_dec (S n) (S i0)). auto. lia. lia.
  simpl in *. destruct i0 eqn:Hi0. simpl in *. inversion H1. subst. intuition.
  destruct i1 eqn:Hi1. simpl. inversion H1. subst. intuition.
  destruct (PeanoNat.Nat.eqb i n0) eqn:Hin0. simpl in *. erewrite closed_tm_open_id; eauto.
  eapply closed_tm_monotone; eauto; lia. lia. simpl in *.
  destruct (PeanoNat.Nat.eqb j n0) eqn:Hjn0. eapply closed_tm_monotone; eauto. lia.
  inversion H1. subst. intuition. inversion H1. subst. intuition.
Qed.

Lemma substitution_gen : forall{n t}, tm_size t < n ->
    forall {Γ' Tf Tx Γ Σ T i j}, has_type (Γ' ++ Tx :: Tf :: Γ) Σ (open_rec_tm j $(S (length Γ)) (open_rec_tm i $(length Γ) (splice (S (length Γ)) (splice (length Γ) t)))) T -> i <> j ->
                        forall {tf}, has_type Γ Σ tf Tf ->
                        forall {tx}, has_type Γ Σ tx Tx ->
                                has_type (Γ' ++ Γ) Σ (open_rec_tm j tx (open_rec_tm i tf t)) T.
  induction n; try lia; destruct t; intros; simpl in *.
  - apply typ_inv_unit in H0. subst. intuition.
  - destruct v.
    + destruct (le_lt_dec (length Γ) i0) eqn:Hle.
      * replace (splice (S (length Γ)) (tvar $(S i0))) with (tvar $(S (S i0))) in H0.
        simpl in *. apply typ_inv_varf in H0. destruct H0 as [U [Hl Hstp]]. apply (t_sub _ _ _ U T).
        apply t_var. erewrite indexr_insert_ge; eauto. erewrite indexr_insert_ge; eauto. simpl. lia.
        eapply strengthen_stp; eauto. eapply strengthen_stp; eauto.
        unfold splice. destruct (le_lt_dec (S (length Γ)) (S i0)) eqn:Heq. auto. lia.
      * erewrite splice_id in H0; intuition. simpl in *.
        apply typ_inv_varf in H0. destruct H0 as [U [Hl Hstp]]. apply (t_sub _ _ _ U T).
        apply t_var. erewrite indexr_insert_lt; eauto. erewrite indexr_insert_lt; eauto. simpl. lia.
        eapply strengthen_stp; eauto. eapply strengthen_stp; eauto.
        Unshelve. auto. auto.
    + simpl in *. destruct (Nat.eqb i i0) eqn:Heq; simpl in *.
      * apply typ_inv_varf in H0. destruct H0 as [U [Hl Hstp]].
        replace (Γ' ++ Tx :: Tf :: Γ) with ((Γ' ++ [Tx]) ++ Tf :: Γ) in Hl.
        rewrite indexr_insert in Hl. inversion Hl. subst. pose (Hc := H2). apply has_type_closed in Hc.
        erewrite closed_tm_open_id; eauto. apply (t_sub _ _ _ U T).
        eapply weaken'; eauto. eapply strengthen_stp; eauto. eapply strengthen_stp; eauto. lia.
        rewrite <- app_assoc. auto.
      * destruct (Nat.eqb j i0) eqn:Heqj. apply typ_inv_varf in H0. destruct H0 as [U [Hl Hstp]].
        replace (S (length Γ)) with (length (Tf :: Γ)) in Hl; eauto.
        rewrite indexr_insert in Hl. inversion Hl. subst. pose (Hc := H3). apply has_type_closed in Hc.
        apply (t_sub _ _ _ U T). eapply weaken'; eauto. eapply strengthen_stp; eauto. eapply strengthen_stp; eauto.
        apply bound_vars_untypable in H0. contradiction.
  - specialize (has_type_closed H2) as Hcltf. specialize (has_type_closed H3) as Hcltx.
    apply typ_inv_abs in H0. destruct H0 as [T3 [T4 [Hc [HTt Hstp]]]]. inversion Hstp. subst.
    apply (t_sub _ _ _ (TFun T3 T4) (TFun T0 T5)). apply t_abs.
    rewrite app_length in *. simpl in *.
    eapply substitution_closed; eauto.
    (* We must swap the openings in the subject so that the IHn on the body t becomes applicable. *)
    unfold open_tm' in *.
    erewrite open_rec_tm_commute' with (t':=tx); eauto. erewrite open_rec_tm_commute' with (t':=tx); eauto.
    erewrite open_rec_tm_commute' with (t':=tf); eauto. erewrite open_rec_tm_commute' with (t':=tf); eauto.
    replace (T3 :: TFun T3 T4 :: Γ' ++ Γ) with ((T3 :: TFun T3 T4 :: Γ') ++ Γ); eauto.
    replace (T3 :: TFun T3 T4 :: Γ' ++ Tx :: Tf :: Γ) with ((T3 :: TFun T3 T4 :: Γ') ++ Tx :: Tf :: Γ) in HTt; eauto.
    eapply IHn; eauto. rewrite <- open_preserves_size. rewrite <- open_preserves_size. lia.
    (* Then, shuffle around the openings/splicings so that they match HTt:*)
    rewrite app_length in *. simpl in *.
    replace (S (length Γ' + length Γ)) with ((S (length Γ')) + length Γ); eauto.
    rewrite splice_open. rewrite splice_open.
    replace (S (S (length Γ') + length Γ)) with (S (length Γ') + (S (length Γ))); eauto.
    rewrite splice_open.
    replace (S (length Γ' + length Γ)) with ((length Γ') + (S (length Γ))); eauto.
    rewrite splice_open.
    erewrite <- open_rec_tm_commute' with (t':=$(length Γ)); intuition.
    erewrite <- open_rec_tm_commute' with (t':=$(length Γ)); intuition.
    erewrite <- open_rec_tm_commute' with (t':=$(S (length Γ))); intuition.
    erewrite <- open_rec_tm_commute' with (t':=$(S (length Γ))); intuition.
    replace (S (S (length Γ') + S (length Γ))) with (S (length Γ' + S (S (length Γ)))); eauto.
    replace (S (length Γ' + S (length Γ))) with (length Γ' + S (S (length Γ))).
    apply HTt. auto. lia. eapply strengthen_stp. eapply strengthen_stp; eauto. Unshelve.
    all: auto.
  - apply typ_inv_app in H0. destruct H0 as [T3 [Hfun Harg]].
    apply (t_app _ _ _ _ T3 T). eapply IHn; eauto. lia. eapply IHn; eauto. lia.
  - apply typ_inv_loc in H0. destruct H0 as [U [Hl Hstp]]. inversion Hstp. subst.
    apply t_loc. auto.
  - apply typ_inv_ref in H0. destruct H0 as [U [Heq HTU]]. subst. apply t_ref.
    eapply IHn; eauto. lia.
  - apply typ_inv_deref in H0. destruct H0 as [U [HTU Hstp]].
    apply (t_sub _ _ _ U T). apply t_deref. eapply IHn; eauto. lia.
    eapply strengthen_stp; eauto. eapply strengthen_stp; eauto.
  - apply typ_inv_assign in H0. destruct H0 as [Heq [U [HTlhs HTrhs]]]. subst.
    apply t_assign with (T:=U); eapply IHn; eauto; lia.
Qed.

Lemma substitution : forall{Γ Tf Tx T Σ t},
    closed_tm 2 (length Γ) (length Σ) t ->
    has_type (Tx :: Tf :: Γ) Σ (open_tm' Γ t) T ->
    forall {tf}, has_type Γ Σ tf Tf -> forall {tx}, has_type Γ Σ tx Tx -> has_type Γ Σ (open_tm tf tx t) T.
  intros. unfold open_tm' in *. unfold open_tm in *. replace Γ with ([] ++ Γ); eauto.
  eapply substitution_gen; eauto. erewrite (@splice_id t); eauto. erewrite splice_id; eauto.
  eapply closed_tm_monotone; eauto; lia.
Qed.

Definition CtxOK (Γ : tenv) (Σ : senv) (σ : store) : Prop :=
  length Σ = length σ /\ forall l v T, indexr l Σ = Some T -> indexr l σ = Some v -> value v /\ has_type Γ Σ v T.

Lemma CtxOK_ext : forall {Γ Σ σ}, CtxOK Γ Σ σ -> forall {v T}, has_type Γ Σ v T -> value v -> CtxOK Γ (T :: Σ) (v :: σ).
  intros. unfold CtxOK in *. split. simpl. lia.
  intros. destruct H as [Hlen Hprev]. destruct (beq_nat l (length σ)) eqn:Heql.
  + simpl in *. rewrite Heql in *. inversion H3. subst.
    rewrite <- Hlen in Heql. rewrite Heql in H2. inversion H2. subst. intuition.
    eapply weaken_store; eauto. apply extends_cons.
  + simpl in *. rewrite Heql in *. rewrite <- Hlen in Heql. rewrite Heql in H2.
    specialize (Hprev _ _ _ H2 H3) as Hprev. intuition.
    eapply weaken_store; eauto. apply extends_cons.
Qed.

Lemma CtxOK_update : forall {Γ Σ σ}, CtxOK Γ Σ σ -> forall {l T}, l < length σ -> indexr l Σ = Some T -> forall {v}, has_type Γ Σ v T -> value v -> CtxOK Γ Σ (update σ l v).
  intros. unfold CtxOK in *. destruct H as [Hlen Hprev].
  split. rewrite <- update_length. auto.
  intros. destruct (Nat.eqb l l0) eqn:Heq.
  - apply beq_nat_true in Heq. subst.
    apply (@update_indexr_hit σ l0 v) in H0. rewrite H1 in H. inversion H. subst.
    rewrite H4 in H0. inversion H0. subst. intuition.
  - apply beq_nat_false in Heq. apply (@update_indexr_miss σ l v l0) in Heq.
    rewrite Heq in H4. eapply Hprev; eauto.
Qed.

Lemma progress : forall {Σ t T}, has_type [] Σ t T -> value t \/ forall {σ}, CtxOK [] Σ σ -> exists t' σ', step t σ t' σ'.
  intros Σ t T HT. remember [] as Γ; induction HT; subst; try solve [left; constructor].
  - inversion H.
  - (*tapp*) right; intuition.
    + specialize (canonical_fun HT1 H1) as Hlam. destruct Hlam as [t' Heq]. subst.
      exists (open_tm (tabs t') t2 t'). exists σ. constructor. auto.
    + apply H1 in H. destruct H as [t' [σ' Hstep]]. exists (tapp t' t2). exists σ'. constructor. auto.
    + apply H0 in H. destruct H as [t' [σ' Hstep]]. exists (tapp t1 t'). exists σ'. constructor; auto.
    + apply H1 in H. destruct H as [t' [σ' Hstep]]. exists (tapp t' t2). exists σ'. constructor. auto.
  - (*tref*) right; intuition.
    + exists &(length σ). exists (t :: σ). constructor. auto.
    + apply H0 in H. destruct H as [t' [σ' Hstep]]. exists (tref t'). exists σ'. constructor. auto.
  - (*tderef*) right; intuition.
    + specialize (canonical_ref HT H0) as Hc. destruct Hc as [l Heq]. subst.
      apply typ_inv_loc in HT. destruct HT as [U [Hlookup Hstp]].
      pose (Hl:=Hlookup).
      unfold CtxOK in H. intuition. apply indexr_var_some' in Hl.
      rewrite H1 in Hl. rewrite <- indexr_var_some in Hl.
      destruct Hl as [v Hl]. exists v. exists σ. constructor. auto.
      specialize (H2 l v U Hlookup Hl). intuition.
    + apply H0 in H. destruct H as [t' [σ' Hstep]]. exists (tderef t'). exists σ'. constructor. auto.
  - (*tassign*) right; intuition.
    + specialize (canonical_ref HT1 H1) as Href. destruct Href as [l Heq]. subst.
      exists tunit. exists (update σ l t2). constructor. apply typ_inv_loc in HT1.
      destruct HT1 as [U [Hl Hstp]]. unfold CtxOK in H. intuition. rewrite <- H2.
      eapply indexr_var_some'. eauto. auto.
    + apply H1 in H. destruct H as [t' [σ' Hstep]]. exists (tassign t' t2). exists σ'. constructor. auto.
    + apply H0 in H. destruct H as [t' [σ' Hstep]]. exists (tassign t1 t'). exists σ'. constructor; auto.
    + apply H1 in H. destruct H as [t' [σ' Hstep]]. exists (tassign t' t2). exists σ'. constructor. auto.
  - (*tsub*) intuition.
Qed.

Lemma preservation : forall {Γ Σ t T}, has_type Γ Σ t T -> forall{σ}, CtxOK Γ Σ σ -> forall {t' σ'}, step t σ t' σ' -> exists Σ', Σ' ⊇ Σ /\ CtxOK Γ Σ' σ' /\ has_type Γ Σ' t' T .
  intros Γ Σ t T HT. induction HT; intros; try solve [inversion H0]; try solve [inversion H1].
  - (*tapp*) inversion H0; subst.
    + (*beta*) inversion H0; subst. pose (Ht2c := HT2). apply has_type_closed in Ht2c.
      * exists Σ. intuition. apply extends_refl.
        apply typ_inv_abs in HT1. destruct HT1 as [T3 [T4 [Hc [HTt Hstp]]]].
        inversion Hstp. subst.
        apply weaken_stp with (T' := TFun T3 T4) in H9.
        specialize (narrowing HTt H9) as HTt'.
        apply (t_sub _ _ _ T4 T2); eauto.
        eapply substitution; eauto.
        apply t_abs; eauto.
      * inversion H7.
      * specialize (values_stuck H6 H8) as Hsp. contradiction.
    + apply (IHHT1 σ H t1' σ') in H6. destruct H6 as [Σ' [Hext [HOK Ht']]].
      exists Σ'. intuition. eapply t_app; eauto. eapply weaken_store; eauto.
    + apply (IHHT2 σ H t2' σ') in H7. destruct H7 as [Σ' [Hext [HOK Ht']]].
      exists Σ'. intuition. eapply t_app; eauto. eapply weaken_store; eauto.
  - (* tref *) inversion H0; subst.
    + exists (T :: Σ). intuition. apply extends_cons. apply CtxOK_ext; auto.
      apply t_loc. unfold CtxOK in H. intuition. rewrite <- H1. apply indexr_head.
    + apply (IHHT σ H t'0 σ') in H2. destruct H2 as [Σ' [Hext [HOK Ht']]].
      exists Σ'. intuition.
  - (* tderef *) inversion H0; subst.
    + exists Σ. intuition. apply extends_refl. apply typ_inv_loc in HT. destruct HT as [U [Hlook Hstp]].
      unfold CtxOK in H. intuition. specialize (H4 _ _ _ Hlook H2). intuition.
      eapply t_sub. eauto. inversion Hstp. subst. apply stp_refl.
    + apply (IHHT σ H t'0 σ') in H2. destruct H2 as [Σ' [Hext [HOK Ht']]].
      exists Σ'. intuition.
  - (* tassign *) inversion H0; subst.
    + exists Σ. intuition. apply extends_refl. eapply CtxOK_update; eauto.
      apply typ_inv_loc in HT1. destruct HT1 as [U [Hl Hstp]].
      inversion Hstp. subst. auto.
    + apply (IHHT1 σ H t1' σ') in H6. destruct H6 as [Σ' [Hext [HOK Ht']]].
      exists Σ'. intuition. eapply t_assign; eauto. eapply weaken_store; eauto.
    + apply (IHHT2 σ H t2' σ') in H7. destruct H7 as [Σ' [Hext [HOK Ht']]].
      exists Σ'. intuition. eapply t_assign; eauto. eapply weaken_store; eauto.
  - (* tsub *) apply (IHHT σ H0 t' σ') in H1. destruct H1 as [Σ' [Hext [HOK Ht']]].
    exists Σ'. intuition. eapply t_sub; eauto. eapply weaken_stp_store; eauto.
Qed.
