-- Prove2me | Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval
-- name    : Monotonicity_Theorem.infinite_definable_set_contains_interval
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T18:25:17.778929+00:00
-- url     : https://prove2.me/theorems/3bb0de0b-164e-4d7b-9c05-9d62f34c16e3
-- title:
--   Infinite definable subsets of the line contain an interval
-- statement:
--   Every infinite definable subset of the one-dimensional coordinate space contains a nonempty open interval.

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.infinite_definable_set_contains_interval {R : Type} (D : DenseLinearOrderNoEndpoints R) (M : OMinimalStructure D) (I : Set (Power R 1)) (hDef : M.S 1 I) (hInf : IsInfinite1 I) : ∃ a b : Endpoint R, Endpoint.lt D a b ∧ (openInterval D a b).Subset I := by sorry
