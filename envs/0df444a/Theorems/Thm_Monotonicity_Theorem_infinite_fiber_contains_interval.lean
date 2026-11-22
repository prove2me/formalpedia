-- Prove2me | Theorems.Thm_Monotonicity_Theorem_infinite_fiber_contains_interval
-- name    : Monotonicity_Theorem.infinite_fiber_contains_interval
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:17:13.989378+00:00
-- url     : https://prove2.me/theorems/711af629-0910-459b-a83d-714398ae7a9e
-- title:
--   Infinite definable fibers contain intervals
-- statement:
--   Every infinite definable one-dimensional fiber contains a nonempty open interval.
-- source:
--   monotonicity.tex, Lemma 1 fiber case

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.infinite_fiber_contains_interval {R : Type} (D : DenseLinearOrderNoEndpoints R)
    (M : OMinimalStructure D) (A : Set (Power R 1))
    (hDef : M.S 1 A) (hInf : IsInfinite1 A) :
    exists a b : Endpoint R, Endpoint.lt D a b /\
      (openInterval D a b).Subset A := by sorry
