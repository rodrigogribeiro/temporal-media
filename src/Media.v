Set Implicit Arguments.

Require Import
        Bool
        EqNat
        PeanoNat
        Tactics.LibTactics
        Tactics.Crush
        Axioms.

(* a type for describing temporal media data *)

Inductive media (A : Type) : Type :=
| Prim : A       -> media A
| Seq  : media A -> media A -> media A
| Par  : media A -> media A -> media A.

Fixpoint durMedia
         {A : Type}
         `{Duration A}(m : media A) : nat :=
  match m with
  | Prim v    => dur v
  | Seq m1 m2 => (durMedia m1) + (durMedia m2)
  | Par m1  _ => durMedia m1 
  end. 

Instance durationMedia
         {A : Type}
         `{Duration A} : Duration (media A)
  :={
      dur := durMedia
    }.

(** Wellformed media types *)

Ltac destruct_reflects :=
  match goal with
  | [H : reflect _ _ |- _] =>
    destruct H ; simpl in * ; destruct_reflects
  | [H : _ |- _] => idtac                                                 
  end.

Ltac boolean_simpl :=
  match goal with
  | [H : context[?x && false]  |- _] => rewrite andb_false_r in H ; boolean_simpl
  | [H : context[?x && true]  |- _] => rewrite andb_true_r in H ; boolean_simpl
  | [|- context[?x && false]] => rewrite andb_false_r ; boolean_simpl
  | [|- context[?x && true]] => rewrite andb_true_r ; boolean_simpl
  | [H : _ |- _] => try congruence
  end.

Section WF.

  Parameter A : Type.
  Context `{HDurA : Duration A}.

  Inductive wf_media : media A -> Prop :=
  | WF_Prim
    : forall (x : A)
    , wf_media (Prim x)
  | WF_Seq
    : forall (m1 m2 : media A)
    , wf_media m1 ->
      wf_media m2 ->
      wf_media (Seq m1 m2)
  | WF_Par
    : forall (m1 m2 : media A)
    , dur m1 = dur m2  ->
      wf_media m1      ->
      wf_media m2      ->
      wf_media (Par m1 m2).
  
  Fixpoint bwf_media (m : media A) : bool :=
    match m with
    | Prim v    => true
    | Seq m1 m2 => (bwf_media m1) &&
                  (bwf_media m2)
    | Par m1 m2 => beq_nat(dur m1) (dur m2) &&
                  (bwf_media m1)           &&
                  (bwf_media m2)
    end.

  Theorem bwf_mediaP
    : forall (m : media A)
    , reflect (wf_media m)
              (bwf_media m).
  Proof.
    Hint Constructors wf_media.
    intros m ; induction m ; apply iff_reflect ;
      splits ; intros H ;
        match type of H with
        | wf_media ?X => inverts* H
        | _           => idtac                          
        end ; simpl in * ; destruct_reflects ; boolean_simpl ;
          try destruct (Nat.eqb_eq (durMedia m1) (durMedia m2)) ;
          eauto.
  Qed.
End WF.

