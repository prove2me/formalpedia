-- Prove2me | Theorems.Thm_Monotonicity_Theorem_lemma_two
-- name    : Monotonicity_Theorem.lemma_two
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T22:02:56.509495+00:00
-- url     : https://prove2.me/theorems/cb78900f-a416-4c38-9b9e-cea6ae969d83
-- title:
--   Lemma 2, injective implies locally monotone
-- statement:
--   An injective definable map has a nonempty open subwindow on which it is strictly increasing or strictly decreasing. Second step of the monotonicity argument.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.lemma_two {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (M : OMinimalStructure R)
    {I B : Set (Power R 1)} (f : DefinableFunction M I B) (hI : Set.Infinite I)
    (hinj : ∀ x y (hx : I x) (hy : I y),
      f.toFun (Subtype.mk x hx) = f.toFun (Subtype.mk y hy) → x = y) :
    ∃ a b : Endpoint R, Endpoint.lt a b ∧
      (∀ x, openInterval a b x → I x) ∧
      ((∀ x (hxI : I x) y (hyI : I y), openInterval a b x → openInterval a b y ->
          Lt1 x y → Lt1 (f.toFun (Subtype.mk x hxI)).1 (f.toFun (Subtype.mk y hyI)).1) ∨
       (∀ x (hxI : I x) y (hyI : I y), openInterval a b x → openInterval a b y ->
          Lt1 x y → Lt1 (f.toFun (Subtype.mk y hyI)).1 (f.toFun (Subtype.mk x hxI)).1)) := by sorry
