-- Prove2me | Theorems.Thm_Monotonicity_Theorem_lemma_one
-- name    : Monotonicity_Theorem.lemma_one
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T22:01:49.462807+00:00
-- url     : https://prove2.me/theorems/1a1f2da7-d0af-4375-9744-f3bcb740778d
-- title:
--   Lemma 1, constant or injective window
-- statement:
--   A definable map on an infinite domain has a nonempty open subwindow on which it is either constant or injective. First step of the monotonicity argument.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.lemma_one {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (M : OMinimalStructure R)
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (hI : Set.Infinite I) :
    ∃ a b : Endpoint R, Endpoint.lt a b ∧
      (openInterval a b).Subset I ∧
      ((∀ x (hxI : I x), openInterval a b x → ∀ y (hyI : I y), openInterval a b y →
          f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI)) ∨
       (∀ x (hxI : I x), openInterval a b x → ∀ y (hyI : I y), openInterval a b y →
          f.toFun (Subtype.mk x hxI) = f.toFun (Subtype.mk y hyI) → x = y)) := by sorry
