-- Prove2me | Theorems.Thm_Monotonicity_Theorem_lemma_three2
-- name    : Monotonicity_Theorem.lemma_three2
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T22:01:57.989145+00:00
-- url     : https://prove2.me/theorems/a015d0d4-7896-435a-af4d-10462fe3a836
-- title:
--   Lemma 3, monotone implies continuous somewhere
-- statement:
--   A strictly monotone definable function is continuous on a subinterval.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.lemma_three2 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (M : OMinimalStructure R)
    {I B : Set (Power R 1)} (f : DefinableFunction M I B)
    (hmono : StrictlyMonotoneOn I B f.toFun) (hI : Set.Infinite I) :
    ∃ a b : Endpoint R, Endpoint.lt a b ∧
      (openInterval a b).Subset I ∧
      (openInterval a b).Subset (ContinuousPoints I
        (FunctionGraph (R := R) (m := 1) (n := 1) (A := I) (B := B) f.toFun)) := by sorry
