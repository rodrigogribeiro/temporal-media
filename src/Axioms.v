Set Implicit Arguments.

Require Import
        Bool
        EqNat
        PeanoNat
        Program.Basics
        Tactics.LibTactics
        Tactics.Crush.

(** type class for equality *)

Reserved Infix "===" (at level 60, no associativity).

Class Eq (A : Type) : Type
  :={
      mequiv : A -> A -> Prop
      where "x '===' y" := (mequiv x y)
    }.

Bind Scope equality_scope with Eq.
Delimit Scope equality_scope with equality.

Notation "x '===' y" := (mequiv x y).

(** type class for functors *)

Open Scope program_scope.

Class Functor (F : Type -> Type) : Type
  :={
      fmap : forall {A B : Type}, (A -> B) -> F A -> F B

    ; fmap_id
      : forall {A : Type}(x : F A)
      , fmap (@id A) x = x

    ; fmap_compose
      : forall {A B C: Type}(g : B -> C)(f : A -> B)(x : F A) 
      , fmap (g ∘ f) x = fmap g (fmap f x)
    }.

(** type class for duration *)

Class Duration (A : Type) : Type
  :={
      dur : A -> nat
    }.

(** a type class for media types and its axioms *)

Reserved Infix ":=:" (at level 50, left associativity).
Reserved Infix ":+:"  (at level 40, left associativity).

Class Temporal (A : Type) `{Duration A, Eq A}: Type
  :={
        (** basic operations on temporal media *) 
        par    : A -> A -> A
        where "x ':=:' y" := (par x y)

      ; seq    : A -> A -> A
        where "x ':+:' y"  := (seq x y)

      ; none   : nat -> A

      ; par_assoc
        : forall (m1 m2 m3 : A),
          m1 :=: (m2 :=: m3) === (m1 :=: m2) :=: m3

      ; seq_assoc
        : forall (m1 m2 m3 : A),
            m1 :+: (m2 :+: m3) === (m1 :+: m2) :+: m3

      ; par_comm
        : forall (m1 m2 : A),
            m1 :=: m2 === m2 :=: m1

      ; none_left
        : forall (m1 : A),
            (none 0) :+: m1 === m1

      ; none_right
        : forall (m1 : A),
            m1 :+: (none 0) === m1

      ; none_par
        : forall (m1 : A),
            (none (dur m1)) :=: m1 ===  m1
      ; none_add
        : forall (n m : nat),
            (none n) :+: (none m) === none (n + m)

      ; seq_par_swap
        : forall (m1 m2 m3 m4 : A),
            dur m1 = dur m3 ->
            dur m2 = dur m4 -> 
            (m1 :+: m2) :=: (m3 :+: m4) === (m1 :=: m3) :+: (m2 :=: m4) 
    }.

Bind Scope temporal_scope with Temporal.
Delimit Scope temporal_scope with temporal.

Notation ":+:" := (@seq _%temporal).
Notation ":=:" := (@par _%temporal).

(** Type classes for media semantics *)

Reserved Infix ":++:" (at level 50, left associativity).
Reserved Infix "@@"  (at level 40, left associativity).

Class Combine (B : Type) `{Eq B, Duration B}: Type
  :={
      concatM : B -> B -> B
      where "x ':++:' y" := (concatM x y)

    ; merge   : B -> B -> B
      where "x '@@' y" := (merge x y)

    ; zero    : nat -> B

    ; concatM_assoc
      : forall (m1 m2 m3 : B)
      , m1 :++: (m2 :++: m3) === (m1 :++: m2) :++: m3

    ; mergeM_assoc
      : forall (m1 m2 m3 : B)
      , m1 @@ (m2 @@ m3) === (m1 @@ m2) @@ m3

    ; concatM_zero_l
      : forall (m1 : B)
      , zero 0 :++: m1 === m1

    ; concatM_zero_r
      : forall (m1 : B)
      , m1 :++: zero 0 === m1

    ; zeroAdd
      : forall (n m : nat)
      , zero n :++: zero m === zero (n + m)
    ; concatM_merge_swap
      : forall (m1 m2 m3 m4 : B)
      , dur m1 = dur m3 ->
        dur m2 = dur m4 ->
        (m1 :++: m2) @@ (m3 :++: m4) === (m1 @@ m3) :++: (m2 @@ m4)
    }.

Class Meaning (A B : Type) `{Combine B, Temporal B, Temporal A} : Type
  :={
      meaning : A -> B

    ; meaning_none
      : forall (n : nat),
        meaning (none n) === zero n
    ; dur_meaning
      : forall (m1 : A),
        dur (meaning m1) = dur m1
    }.
