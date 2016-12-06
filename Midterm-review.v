Require Export SFBook.

(* Prove the following basic property of doubling *)

Theorem double_Sm : forall (n m : nat),
  n = S m -> n + n = S (S (m + m)).
Proof.
  intros n m H.
  rewrite H.
  simpl.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.


(* Prove the following using destruct (either explicitly or implicitly). *)

Theorem andb_false_l : forall b, b && true = b.
Proof.
  intros []; reflexivity.
Qed.

(* Prove without destruct (either explicit or implicit). *)

Theorem andb_false_l' : forall b, b && true = b.
Proof.
  intros.
  rewrite andb_commutative.
  simpl.
  reflexivity.
Qed.


(* ******************************************************************************** *)

(* The following is the erroneous "mult3b" function from the written part. Fix it (removing
   the "Fail" modifier)! *)

Fixpoint mult3b (n : nat) : bool :=
  match n with
   | O => true
   | S (S (S n')) => mult3b n'
   | _ => false
  end.

(* Now use your function and "filter" to create a new function that takes a list of nats,
   and returns a list containing only those elements that are multiples of 3. *)

Definition extract_mult3s (l : list nat) : (list nat) :=
  filter mult3b l.

Example test_extract_mult3s1 : extract_mult3s [1;3;9;2;7;3;5;0] = [3;9;3;0].
Proof. reflexivity. Qed.

(* Next, use filter and an anonymous function to create a list that contains only those
   elements that are one smaller than a multiple of 3. *)

Definition extract_2mod3 (l : list nat) : (list nat) :=
  filter (fun n:nat => mult3b (S n)) l.

Example test_2mod3_1 : extract_2mod3 [1;3;9;2;7;3;5;0] = [2;5].
Proof. reflexivity. Qed.

(* ******************************************************************************** *)

(* Define a function pair_flatten that takes a list of pairs of some type X, and
   produces a list of X that contains each individual item (no pairs). In other words,
   if called with the (list (nat*nat)) [(1,5);(2,4);(7,9)] it should return the list
   [1;5;2;4;7;9] *)

(* FILL IN HERE *)

(* State and prove a theorem [pair_flatten_len] that for any list of pairs [l] given
   to [pair_flatten_len], the length of the produced list is twice the length of the
   original list. *)

(* FILL IN HERE *)

(* ******************************************************************************** *)

(* The following definition generalizes the definition of "oddmembers" from the book using
   the polymorphic list type. *)

Fixpoint oddmembers (l : list nat) : list nat :=
  match l with
  | nil => nil
  | h::t => match (evenb h) with
            | true => oddmembers t
            | false => h::(oddmembers t)
            end
  end.

(* Prove the following theorem - note: maybe slightly too complex for the exam, but maybe
   as a final "challenge" problem (extra credit?) *)

Theorem bigger_logic : forall (l : list nat),
  In 7 l <-> In 7 (oddmembers l).
Proof.
  (* FILL IN HERE *) Admitted.






