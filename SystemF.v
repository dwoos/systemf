Require Import Arith.
Require Import Tactics.
Require Import List.
Import ListNotations.

Inductive var :=
| mkVar : nat -> var.

Lemma var_eq_dec :
  forall x y : var,
    {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Defined.

Definition var_to_nat v :=
  match v with
    | mkVar n => n
  end.

Inductive tvar :=
| mkTVar : nat -> tvar.

Lemma tvar_eq_dec :
  forall x y : tvar,
    {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Defined.

Definition tvar_to_nat v :=
  match v with
    | mkTVar n => n
  end.

Section Map.
  Variable A : Type.
  Record Map :=
    {A_eq_dec : forall x y : A, {x = y} + {x <> y};
     _map : list (A * A)}.

  Definition empty (A_eq_dec : forall x y : A, {x = y} + {x <> y}) :=
    Build_Map A_eq_dec [].

  Fixpoint lkup1' (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (m : list (A * A)) (a : A) :=
    match m with
    | [] => None
    | (x, y) :: m' =>
      if A_eq_dec a x then Some y else lkup1' A_eq_dec m' a
    end.

  Fixpoint lkup2' (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (m : list (A * A)) (a : A) :=
    match m with
    | [] => None
    | (y, x) :: m' =>
      if A_eq_dec a x then Some y else lkup2' A_eq_dec m' a
    end.

  Definition lkup1 (m : Map) (a : A) :=
    lkup1' (A_eq_dec m) (_map m) a.

  Definition lkup2 (m : Map) (a : A) :=
    lkup2' (A_eq_dec m) (_map m) a.

  Definition update' l (x y: A) :=
    (x, y) :: l.

  Definition update (m : Map) (x y : A) :=
    Build_Map (A_eq_dec m) (update' (_map m) x y).

  Lemma lkup1_update_eq :
    forall m x v,
      lkup1 (update m x v) x = Some v.
  Proof.
    unfold lkup1; unfold update.
    cbn. induction m; intros; simpl in *; intuition.
    break_if; subst; congruence.
  Qed.

  Lemma lkup2_update_eq :
    forall m x v,
      lkup2 (update m v x) x = Some v.
  Proof.
    unfold lkup1; unfold update.
    cbn. induction m; intros; simpl in *; intuition.
    break_if; subst; congruence.
  Qed.

  Lemma lkup1_update_neq :
    forall m x y v,
      x <> y ->
      lkup1 (update m x v) y = lkup1 m y.
  Proof.
    unfold lkup1; unfold update.
    cbn. destruct m; intros; simpl in *; intuition.
    break_if; subst; congruence.
  Qed.

  Lemma lkup2_update_neq :
    forall m x y v,
      x <> y ->
      lkup2 (update m v x) y = lkup2 m y.
  Proof.
    unfold lkup2; unfold update.
    cbn. destruct m; intros; simpl in *; intuition.
    break_if; subst; congruence.
  Qed.

  Lemma lkup1_empty :
    forall e x,
      lkup1 (empty e) x = None.
  Proof.
    unfold lkup1, empty. simpl. intuition.
  Qed.

  Lemma lkup2_empty :
    forall e x,
      lkup2 (empty e) x = None.
  Proof.
    unfold lkup2, empty. simpl. intuition.
  Qed.
    
  Definition inverse (m : Map) :=
    Build_Map (A_eq_dec m) (map (fun kw => (snd kw, fst kw)) (_map m)).

  Lemma lkup_inverse :
    forall m x,
      lkup1 m x = lkup2 (inverse m) x.
  Proof.
    unfold lkup1, lkup2. cbn. intros.
    destruct m; intros; simpl in *; intuition.
    induction _map0; intros; simpl in *; intuition.
    simpl in *.
    break_if; simpl in *; repeat find_rewrite; intuition.
  Qed.


  Lemma lkup_inverse' :
    forall m x,
      lkup2 m x = lkup1 (inverse m) x.
  Proof.
    unfold lkup1, lkup2. cbn. intros.
    destruct m; intros; simpl in *; intuition.
    induction _map0; intros; simpl in *; intuition.
    simpl in *.
    break_if; simpl in *; repeat find_rewrite; intuition.
  Qed.

  Lemma inverse_update :
    forall m x y,
      inverse (update m x y) =
      update (inverse m) y x.
  Proof.
    intros. unfold inverse, update. simpl. f_equal.
  Qed.

  Definition invertible (m : Map) :=
    forall x y,
      lkup1 m x = Some y ->
      lkup2 m y = Some x.

  Lemma invertible_singleton :
    forall eq x y,
      invertible (update (empty eq) x y).
  Proof.
    intros. unfold invertible, lkup1, lkup2, update, empty. simpl.
    intros; repeat break_if; subst; simpl in *; congruence.
  Qed.

  Lemma map_ind :
    forall (P : Map -> Prop),
      (forall A_eq_dec, P (empty A_eq_dec)) ->
      (forall m x y,
          P m ->
          P (update m x y)) ->
      forall m, P m.
  Proof.
    intros. destruct m as [? M]. induction M.
    - fold (empty A_eq_dec0). auto.
    - destruct a.
      assert (P (update (Build_Map A_eq_dec0 M) a a0)) as HP by auto.
      unfold update, update' in HP.
      simpl in HP. auto.
  Qed.
      
End Map.

Arguments update {_} _ _ _ : simpl never.
Arguments lkup1 {_} _ _ : simpl never.
Arguments lkup2 {_} _ _ : simpl never.
Arguments empty {_} _ : simpl never.
Arguments inverse {_} _ : simpl never.
Arguments A_eq_dec {_} _ _ _.
Arguments invertible {_} _ : simpl never.

Ltac destruct_lkup1_update :=
  match goal with
  | H : context [lkup1 (update ?m ?x _) ?y] |- _ =>
    destruct (A_eq_dec m x y); [subst; rewrite lkup1_update_eq in *|rewrite lkup1_update_neq in * by auto]
  | |- context [lkup1 (update ?m ?x _) ?y] =>
    destruct (A_eq_dec m x y); [subst; rewrite lkup1_update_eq in *|rewrite lkup1_update_neq in * by auto]
  end.

Ltac destruct_lkup2_update :=
  match goal with
  | H : context [lkup2 (update ?m _ ?x) ?y] |- _ =>
    destruct (A_eq_dec m x y); [subst; rewrite lkup2_update_eq in *|rewrite lkup2_update_neq in * by auto]
  | |- context [lkup2 (update ?m _ ?x) ?y] =>
    destruct (A_eq_dec m x y); [subst; rewrite lkup2_update_eq in *|rewrite lkup2_update_neq in * by auto]
  end.

Lemma lkup1_update_update :
  forall (A : Type) (m : Map A) x y v1 v2,
    lkup1 (update (update m x v1) x v2) y =
    lkup1 (update m x v2) y.
Proof.
  intros. destruct (A_eq_dec m x y).
  - subst. repeat rewrite lkup1_update_eq. auto.
  - repeat rewrite lkup1_update_neq; auto.
Qed.

Lemma lkup2_update_update :
  forall (A : Type) (m : Map A) x y v1 v2,
    lkup2 (update (update m v1 x) v2 x) y =
    lkup2 (update m v2 x) y.
Proof.
  intros. destruct (A_eq_dec m x y).
  - subst. repeat rewrite lkup2_update_eq. auto.
  - repeat rewrite lkup2_update_neq; auto.
Qed.

Lemma invertible_update :
  forall A (m : Map A) x y,
    invertible m ->
    lkup2 m y = None ->
    invertible (update m x y).
Proof.
  intros.
  unfold invertible in *.
  intros.
  destruct_lkup1_update.
  - find_inversion.
    rewrite lkup2_update_eq. auto.
  - destruct_lkup2_update.
    + erewrite H in H0; eauto. congruence.
    + erewrite H; eauto.
Qed.
  
Inductive type :=
| TUnit : type
| TVar : tvar -> type
| TForall : tvar -> type -> type
| TArrow : type -> type -> type.

Inductive term :=
| Unit : term
| Var : var -> term
| TyApp : term -> type -> term
| App : term -> term -> term
| Lam : var -> type -> term -> term
| Bam : tvar -> term -> term.


Fixpoint talpha_equiv ty1 ty2 (equiv_tvars : Map tvar) :=
  match (ty1, ty2) with
    | (TUnit, TUnit) => true
    | (TVar v, TVar v') => match lkup1 equiv_tvars v with
                            | Some v => if tvar_eq_dec v v' then true else false
                            | None => false
                          end
    | (TForall v1 ty1, TForall v2 ty2) =>
      talpha_equiv ty1 ty2 (update equiv_tvars v1 v2)
    | (TArrow ty1l ty1r, TArrow ty2l ty2r) =>
      andb (talpha_equiv ty1l ty2l equiv_tvars)
           (talpha_equiv ty1r ty2r equiv_tvars)
    | _ => false
  end.

Fixpoint alpha_equiv' t1 t2 (equiv_vars : Map var) (equiv_tvars : Map tvar) : bool :=
  match (t1, t2) with
    | (Unit, Unit) => true
    | (Var v, Var v') => match lkup1 equiv_vars v with
                          | Some v => if var_eq_dec v v' then true else false
                          | None => false
                        end
    | (TyApp t1' ty1, TyApp t2' ty2) =>
      andb (alpha_equiv' t1' t2' equiv_vars equiv_tvars) (talpha_equiv ty1 ty2 equiv_tvars)
    | (Lam v1 ty1 t1', Lam v2 ty2 t2') =>
      andb (alpha_equiv' t1' t2'
                         (update equiv_vars v1 v2)
                         equiv_tvars)
           (talpha_equiv ty1 ty2 equiv_tvars)
    | (Bam v1 t1', Bam v2 t2') =>
      alpha_equiv' t1' t2' equiv_vars
                   (update equiv_tvars v1 v2)
    | (App t1l t1r, App t2l t2r) =>
      andb (alpha_equiv' t1l t2l equiv_vars equiv_tvars) (alpha_equiv' t1r t2r equiv_vars equiv_tvars)
    | _ => false
  end.

Definition alpha_equiv t1 t2 equiv_vars equiv_tvars :=
  andb (alpha_equiv' t1 t2 equiv_vars equiv_tvars)
       (alpha_equiv' t2 t1 (inverse equiv_vars) (inverse equiv_tvars)).

Coercion Var : var >-> term.
Coercion TVar : tvar >-> type.
Coercion mkVar : nat >-> var.
Coercion mkTVar : nat >-> tvar.

Fixpoint max_var (t : term) : var :=
  match t with
    | Unit => 0
    | Var v => v
    | TyApp t' _ => max_var t'
    | App t1 t2 => max (var_to_nat (max_var t1)) (var_to_nat (max_var t2))
    | Lam v _ t' => max (var_to_nat v) (var_to_nat (max_var t'))
    | Bam _ t' => max_var t'
  end.

Definition emptyv := empty var_eq_dec.
Definition emptytv := empty tvar_eq_dec.

Notation vX := 1.
Notation vY := 2.
Notation vZ := 3.

Notation vAlpha := 1.
Notation vBeta := 2.

Eval compute in (alpha_equiv (Bam vAlpha (Lam vX vAlpha vX)) (Bam vAlpha (Lam vY vAlpha vY)) emptyv emptytv).

Eval compute in (alpha_equiv (Lam vX TUnit (Lam vY TUnit vX)) (Lam vX TUnit (Lam vX TUnit vX)) emptyv emptytv).


Inductive free : var -> term -> Prop :=
| free_var : forall v, free v v
| free_tyapp : forall v t ty, free v t -> free v (TyApp t ty)
| free_app_l : forall v t1 t2, free v t1 -> free v (App t1 t2)
| free_app_r : forall v t1 t2, free v t2 -> free v (App t1 t2)
| free_lam : forall v v' ty t', v <> v' -> free v t' -> free v (Lam v' ty t')
| free_bam : forall v tv t', free v t' -> free v (Bam tv t').

Inductive tfree : tvar -> type -> Prop :=
| tfree_tvar : forall v, tfree v v
| tfree_forall : forall v v' ty, v <> v' -> tfree v ty -> tfree v (TForall v' ty)
| tfree_arrow_l : forall v ty1 ty2, tfree v ty1 -> tfree v (TArrow ty1 ty2)
| tfree_arrow_r : forall v ty1 ty2, tfree v ty2 -> tfree v (TArrow ty1 ty2).

Inductive tfree_term : tvar -> term -> Prop :=
| tfree_tyapp_l : forall v t ty, tfree_term v t -> tfree_term v (TyApp t ty)
| tfree_tyapp_r : forall v t ty, tfree v ty -> tfree_term v (TyApp t ty)
| tfree_app_l : forall v t1 t2, tfree_term v t1 -> tfree_term v (App t1 t2)
| tfree_app_r : forall v t1 t2, tfree_term v t2 -> tfree_term v (App t1 t2)
| tfree_lam_ty : forall v v' ty t', tfree v ty -> tfree_term v (Lam v' ty t')
| tfree_lam_t : forall v v' ty t', tfree_term v t' -> tfree_term v (Lam v' ty t')
| tfree_bam : forall tv tv' t', tv <> tv' -> tfree_term tv t' -> tfree_term tv (Bam tv' t').

Definition closed t :=
  forall v tv,
    ~ free v t /\ ~ tfree_term tv t.

Definition closedt ty :=
  forall tv,
    ~ tfree tv ty.

Lemma closed_free :
  forall v t,
    free v t ->
    ~ closed t.
Proof.
  unfold closed.
  intuition.
  specialize (H0 v 0).
  intuition.
Qed.

Lemma closed_tfree :
  forall v t,
    tfree_term v t ->
    ~ closed t.
Proof.
  unfold closed.
  intuition.
  specialize (H0 0 v).
  intuition.
Qed.

Lemma talpha_equiv_refl :
  forall ty tvars,
    (forall v, tfree v ty -> lkup1 tvars v = Some v) ->
    talpha_equiv ty ty tvars = true.
Proof.
  induction ty; intros; simpl in *; intuition.
  - break_match;
    find_higher_order_rewrite; try solve [constructor]; try congruence.
    find_inversion; break_match; congruence.
  - apply IHty. intros.
    destruct_lkup1_update; auto.
    find_higher_order_rewrite; auto.
    constructor; auto.
  - apply Bool.andb_true_iff.
    intuition.
    + apply IHty1. intros.
      find_higher_order_rewrite; auto.
      constructor; auto.
    + apply IHty2. intros.
      find_higher_order_rewrite; auto.
      solve [constructor; auto].
Qed.
      
Lemma closedt_talpha_equiv_refl :
  forall ty,
    closedt ty ->
    talpha_equiv ty ty emptytv = true.
Proof.
  intros.
  apply talpha_equiv_refl.
  intros.
  exfalso. eapply H; eauto.
Qed.

Lemma alpha_equiv'_refl :
  forall t vars tvars,
    (forall v, free v t -> lkup1 vars v = Some v) ->
    (forall tv, tfree_term tv t -> lkup1 tvars tv = Some tv) ->
    alpha_equiv' t t vars tvars = true.
Proof.
  induction t; intros; simpl in *; intuition.
  - break_match; find_higher_order_rewrite; try solve [constructor]; try congruence.
    find_inversion; break_match; congruence.
  - apply Bool.andb_true_iff. intuition.
    + apply IHt;
      intros;
      find_higher_order_rewrite; auto;
        solve [constructor; auto].
    + apply talpha_equiv_refl.
      intros.
      find_higher_order_rewrite; auto;
        solve [constructor; auto].
  - apply Bool.andb_true_iff. intuition.
    + apply IHt1;
      intros;
      find_higher_order_rewrite; auto;
        solve [constructor; auto].
    + apply IHt2;
      intros;
      find_higher_order_rewrite; auto;
        solve [constructor; auto].
  - apply Bool.andb_true_iff. intuition.
    + apply IHt;
        intros; try destruct_lkup1_update; subst; auto;
          find_higher_order_rewrite; auto;
            solve [constructor; auto].
    + apply talpha_equiv_refl.
      intros;
        find_higher_order_rewrite; auto;
          solve [constructor; auto].
  - apply IHt; intros.
    + find_higher_order_rewrite; auto;
        solve [constructor; auto].
    + destruct_lkup1_update; try congruence.
      find_higher_order_rewrite; auto;
        solve [constructor; auto].
Qed.
      
Lemma closed_alpha_equiv_refl :
  forall t,
    closed t ->
    alpha_equiv t t emptyv emptytv = true.
Proof.
  intros.
  unfold alpha_equiv.
  rewrite Bool.andb_diag.
  apply alpha_equiv'_refl; intros; exfalso.
  - eapply closed_free; eauto.
  - eapply closed_tfree; eauto.
Qed.

Fixpoint trename_all (ty : type) (next : tvar) (tvars : Map tvar) :=
  match ty with
  | TVar tv => match lkup1 tvars tv with
              | Some tv' => Some (TVar tv')
              | None => None
              end
  | TForall tv ty' =>
    match (trename_all ty' (S (tvar_to_nat next))
                       (update tvars tv next)) with
    | Some ty'' =>
      Some (TForall next ty'')
    | None => None
    end
  | TArrow ty1 ty2 =>
    match (trename_all ty1 next tvars, trename_all ty2 next tvars) with
    | (Some ty1', Some ty2') =>
      Some (TArrow ty1' ty2')
    | _ => None
    end
  | _ => Some ty
  end.

Lemma trename_all_alpha_equiv :
  forall ty next tvars,
    (forall tv, tfree tv ty ->
           exists tv',
             lkup1 tvars tv = Some tv') ->
    exists ty',
      trename_all ty next tvars = Some ty' /\
      talpha_equiv ty ty' tvars = true.
Proof.
  induction ty; intros; simpl in *; intuition.
  - eexists; intuition eauto.
  - specialize (H t). conclude_using constructor.
    break_exists. repeat find_rewrite.
    eexists; intuition eauto.
    break_if; congruence.
  - match goal with
    | |- context [trename_all _ ?x ?y] =>
      specialize (IHty x y)
    end.
    intuition. forward IHty.
    + intros. destruct_lkup1_update; try solve [eexists; eauto].
      apply H.
      constructor; auto.
    + concludes. break_exists.
      intuition.
      find_rewrite.
      eexists; intuition eauto.
  - match goal with
    | |- context [trename_all ty1 ?x ?y] =>
      specialize (IHty1 x y)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H;
        constructor; auto).
    match goal with
    | |- context [trename_all ty2 ?x ?y] =>
      specialize (IHty2 x y)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H;
        constructor; auto).
    break_exists. intuition.
    repeat find_rewrite.
    eexists; intuition eauto.
    apply Bool.andb_true_iff. intuition.
Qed.

Require Import Omega.

Lemma trename_all_alpha_equiv' :
  forall ty (next : nat) (tvars : Map tvar),
    invertible tvars ->
    (forall x, next <= x -> lkup2 tvars x = None) ->
    (forall tv, tfree tv ty ->
           exists tv',
             lkup1 tvars tv = Some tv') ->
    exists ty',
      trename_all ty next tvars = Some ty' /\
      talpha_equiv ty' ty (inverse tvars) = true.
Proof.
  induction ty; intros; simpl in *; intuition.
  - eexists; intuition eauto.
  - specialize (H1 t). conclude_using constructor.
    break_exists. repeat find_rewrite.
    eexists; intuition eauto. simpl.
    rewrite <- lkup_inverse'.
    unfold invertible in *.
    find_apply_hyp_hyp. find_rewrite.
    break_if; congruence.
  - match goal with
    | |- context [trename_all _ _ ?y] =>
      specialize (IHty (S next) y)
    end.
    conclude_using ltac:(eauto using invertible_update).
    forward IHty.
    { intros.
      assert (next <> x) by omega.
      rewrite lkup2_update_neq; [apply H0; omega|].
      intro. find_inversion. auto. }
    concludes.
    forward IHty.
    {
      intros. destruct_lkup1_update; try solve [eexists; eauto].
      apply H1.
      constructor; auto.
    }
    concludes. break_exists.
    intuition.
    find_rewrite.
    eexists; intuition eauto.
  - match goal with
    | |- context [trename_all ty1 ?x ?y] =>
      specialize (IHty1 next y)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H1;
        constructor; auto).
    match goal with
    | |- context [trename_all ty2 ?x ?y] =>
      specialize (IHty2 next y)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H1;
        constructor; auto).
    break_exists. intuition.
    repeat find_rewrite.
    eexists; intuition eauto.
    apply Bool.andb_true_iff. intuition.
Qed.

Fixpoint rename_all (t : term) (next : var) (vars : Map var) (tnext : tvar) (tvars : Map tvar) :=
  match t with
  | Var v => match lkup1 vars v with
            | Some v' => Some (Var v')
            | None => None
            end
  | TyApp t' ty => match (rename_all t' next vars tnext tvars, trename_all ty tnext tvars) with
                  | (Some t'', Some ty') => Some (TyApp t'' ty')
                  | _ => None
                  end
  | App t1 t2 => match (rename_all t1 next vars tnext tvars, rename_all t2 next vars tnext tvars) with
                | (Some t1', Some t2') => Some (App t1' t2')
                | _ => None
                end
  | Lam v ty t' => match (rename_all t' (S (var_to_nat next))
                                    (update vars v next) tnext tvars,
                         trename_all ty tnext tvars) with
                  | (Some t'', Some ty') =>
                    Some (Lam next ty' t'')
                  | _ => None
                  end
  | Bam tv t' => match rename_all t' next vars (S (tvar_to_nat tnext))
                                 (update tvars tv tnext) with
                | Some t'' =>
                  Some (Bam tnext t'')
                | _ => None
                end
  | _ => Some t
  end.


Lemma rename_all_alpha_equiv'_l :
  forall t next vars tnext tvars,
    (forall v, free v t ->
          exists v',
            lkup1 vars v = Some v') ->
    (forall tv, tfree_term tv t ->
           exists tv',
             lkup1 tvars tv = Some tv') ->
    exists t',
      rename_all t next vars tnext tvars = Some t' /\
      alpha_equiv' t t' vars tvars = true.
Proof.
  induction t; intros; simpl in *; intuition.
  - eexists; intuition eauto.
  - specialize (H v). conclude_using constructor.
    break_exists. repeat find_rewrite.
    eexists; intuition eauto.
    break_if; congruence.
  - match goal with
    | |- context [rename_all _ ?x ?y ?z ?w] =>
      specialize (IHt x y z w)
    end.
    forward IHt.
    { intros. 
      apply H.
      constructor; auto.
    } concludes.
    forward IHt.
    { intros. 
      apply H0.
      constructor; auto.
    } concludes.
    break_exists.
    intuition.
    find_rewrite.
    pose proof trename_all_alpha_equiv t0 tnext tvars.
    forwards.
    {
      intros.
      apply H0.
      solve [constructor; auto].
    }
    concludes.
    break_exists. intuition.
    find_rewrite.
    eexists; intuition eauto.
    apply Bool.andb_true_iff. intuition.
  - match goal with
    | |- context [rename_all t1 ?x ?y ?z ?w] =>
      specialize (IHt1 x y z w)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H;
        constructor; auto).
    conclude_using ltac:(
        intros;
        apply H0;
        constructor; auto).
    match goal with
    | |- context [rename_all t2 ?x ?y ?z ?w] =>
      specialize (IHt2 x y z w)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H;
        constructor; auto).
    conclude_using ltac:(
        intros;
        apply H0;
        constructor; auto).
    break_exists. intuition.
    repeat find_rewrite.
    eexists; intuition eauto.
    apply Bool.andb_true_iff. intuition.
  - match goal with
    | |- context [rename_all _ ?x ?y ?z ?w] =>
      specialize (IHt x y z w)
    end.
    forward IHt.
    { intros.
      destruct_lkup1_update; eauto.
      apply H.
      constructor; auto.
    } concludes.
    forward IHt.
    { intros. 
      apply H0.
      solve [constructor; auto].
    } concludes.
    break_exists.
    intuition.
    find_rewrite.
    pose proof trename_all_alpha_equiv t tnext tvars.
    forwards.
    {
      intros.
      apply H0.
      solve [constructor; auto].
    }
    concludes.
    break_exists. intuition.
    find_rewrite.
    eexists; intuition eauto.
    apply Bool.andb_true_iff. intuition.
  - match goal with
    | |- context [rename_all _ ?x ?y ?z ?w] =>
      specialize (IHt x y z w)
    end.
    forward IHt.
    { intros.
      apply H.
      constructor; auto.
    } concludes.
    forward IHt.
    { intros. 
      destruct_lkup1_update; eauto.
      apply H0.
      solve [constructor; auto].
    } concludes.
    break_exists.
    intuition.
    find_rewrite.
    eexists; intuition eauto.
Qed.



Lemma rename_all_alpha_equiv'_r :
  forall t (next : nat) (vars : Map var) (tnext : nat) (tvars : Map tvar),
    invertible vars ->
    invertible tvars ->
    (forall x, next <= x -> lkup2 vars x = None) ->
    (forall x, tnext <= x -> lkup2 tvars x = None) ->
    (forall v, free v t ->
          exists v',
            lkup1 vars v = Some v') ->
    (forall tv, tfree_term tv t ->
           exists tv',
             lkup1 tvars tv = Some tv') ->
    exists t',
      rename_all t next vars tnext tvars = Some t' /\
      alpha_equiv' t' t (inverse vars) (inverse tvars) = true.
Proof.
  induction t; intros; simpl in *; intuition.
  - eexists; intuition eauto.
  - specialize (H3 v). conclude_using constructor.
    break_exists. repeat find_rewrite.
    eexists; intuition eauto.
    simpl.
    rewrite <- lkup_inverse'.
    unfold invertible in H.
    erewrite H by eauto.
    break_if; congruence.
  - match goal with
    | |- context [rename_all _ ?x ?y ?z ?w] =>
      specialize (IHt next y tnext w)
    end.
    intuition.
    forwards.
    { intros. 
      apply H3.
      constructor; auto.
    } concludes.
    forward H6.
    { intros. 
      apply H4.
      constructor; auto.
    } concludes.
    break_exists.
    intuition.
    find_rewrite.
    pose proof trename_all_alpha_equiv' t0 tnext tvars.
    intuition.
    forwards.
    {
      intros.
      apply H4.
      solve [constructor; auto].
    }
    concludes.
    break_exists. intuition.
    find_rewrite.
    eexists; intuition eauto.
    apply Bool.andb_true_iff. intuition.
  - match goal with
    | |- context [rename_all t1 ?x ?y ?z ?w] =>
      specialize (IHt1 next y tnext w)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H3;
        constructor; auto).
    conclude_using ltac:(
        intros;
        apply H4;
        constructor; auto).
    match goal with
    | |- context [rename_all t2 ?x ?y ?z ?w] =>
      specialize (IHt2 next y tnext w)
    end.
    intuition.
    conclude_using ltac:(
        intros;
        apply H3;
        constructor; auto).
    conclude_using ltac:(
        intros;
        apply H4;
        constructor; auto).
    break_exists. intuition.
    repeat find_rewrite.
    eexists; intuition eauto.
    apply Bool.andb_true_iff. intuition.
  - match goal with
    | |- context [rename_all _ ?x ?y ?z ?w] =>
      specialize (IHt (S next) y tnext w)
    end.
    conclude_using ltac:(eauto using invertible_update).
    intuition.
    forward H5.
    {
      intros.
      assert (next <> x) by omega.
      rewrite lkup2_update_neq; [apply H1; omega|].
      intro. find_inversion. auto. } concludes.
    conclude_using eauto.
    forward H5.
    { intros.
      destruct_lkup1_update; eauto.
      apply H3.
      constructor; auto.
    } concludes.
    forward H5.
    { intros. 
      apply H4.
      solve [constructor; auto].
    } concludes.
    break_exists.
    intuition.
    find_rewrite.
    pose proof trename_all_alpha_equiv' t tnext tvars. intuition.
    forwards.
    {
      intros.
      apply H4.
      solve [constructor; auto].
    }
    concludes.
    break_exists. intuition.
    find_rewrite.
    eexists; intuition eauto. simpl.
    apply Bool.andb_true_iff. intuition.
  - match goal with
    | |- context [rename_all _ ?x ?y ?z ?w] =>
      specialize (IHt next y (S tnext) w)
    end. intuition.
    conclude_using ltac:(eauto using invertible_update).
    intuition.
    forward H6.
    {
      intros.
      assert (tnext <> x) by omega.
      rewrite lkup2_update_neq; [apply H2; omega|].
      intro. find_inversion. auto. } concludes.
    forward H6.
    { intros.
      apply H3.
      constructor; auto.
    } concludes.
    forward H6.
    { intros. 
      destruct_lkup1_update; eauto.
      apply H4.
      solve [constructor; auto].
    } concludes.
    break_exists.
    intuition.
    find_rewrite.
    eexists; intuition eauto.
Qed.

Lemma rename_all_alpha_equiv' :
  forall t (next : nat) (vars : Map var) (tnext : nat) (tvars : Map tvar),
    invertible vars ->
    invertible tvars ->
    (forall x, next <= x -> lkup2 vars x = None) ->
    (forall x, tnext <= x -> lkup2 tvars x = None) ->
    (forall v, free v t ->
          exists v',
            lkup1 vars v = Some v') ->
    (forall tv, tfree_term tv t ->
           exists tv',
             lkup1 tvars tv = Some tv') ->
    exists t',
      rename_all t next vars tnext tvars = Some t' /\
      alpha_equiv t t' vars tvars = true.
Proof.
  intros.
  find_copy_eapply_lem_hyp rename_all_alpha_equiv'_l; eauto.
  find_copy_eapply_lem_hyp rename_all_alpha_equiv'_r; eauto.
  break_exists; intuition; repeat find_rewrite.
  find_inversion.
  eexists; intuition eauto.
  unfold alpha_equiv.
  apply Bool.andb_true_iff.
  intuition.
Qed.

Lemma rename_all_alpha_equiv :
  forall t (next : nat) (vars : Map var) (tnext : nat) (tvars : Map tvar),
    closed t ->
    exists t',
      rename_all t 1 emptyv 1 emptytv = Some t' /\
      alpha_equiv t t' emptyv emptytv = true.
Proof.
  intros. unfold emptyv, emptytv.
  apply rename_all_alpha_equiv'.
  - unfold invertible. intros.
    rewrite lkup1_empty in *.
    congruence.
  -  unfold invertible. intros.
    rewrite lkup1_empty in *.
    congruence.
  - intros.
    rewrite lkup2_empty. auto.
  - intros.
    rewrite lkup2_empty. auto.
  - intros.
    exfalso; eapply closed_free; eauto.
  - intros.
    exfalso; eapply closed_tfree; eauto.
Qed.
