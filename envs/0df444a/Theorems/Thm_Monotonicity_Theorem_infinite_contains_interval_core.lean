-- Prove2me | Theorems.Thm_Monotonicity_Theorem_infinite_contains_interval_core
-- name    : Monotonicity_Theorem.infinite_contains_interval_core
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T17:45:06.121964+00:00
-- url     : https://prove2.me/theorems/3c8c1f4f-afc6-47d4-a5d0-e200f867cf14
-- title:
--   Infinite finite-union sets contain an interval
-- statement:
--   If a one-dimensional set is a finite union of points and intervals and is infinite, then it contains a nonempty open interval.

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.infinite_contains_interval_core {R : Type} (D : DenseLinearOrderNoEndpoints R) (A : Set (Power R 1)) (hDef : FiniteUnionOfPointsAndIntervals D A) (hInf : IsInfinite1 A) : exists a b : Endpoint R, Endpoint.lt D a b ∧ forall x, openInterval D a b x -> A x := by sorry
