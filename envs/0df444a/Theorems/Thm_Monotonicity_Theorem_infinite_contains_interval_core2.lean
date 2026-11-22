-- Prove2me | Theorems.Thm_Monotonicity_Theorem_infinite_contains_interval_core2
-- name    : Monotonicity_Theorem.infinite_contains_interval_core2
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T23:46:33.630578+00:00
-- url     : https://prove2.me/theorems/5109985e-0eee-4623-a88a-1c36e8f69989
-- title:
--   Infinite unions contain an interval
-- statement:
--   An infinite set that is a finite union of points and intervals contains a nondegenerate open interval: empty and point cases are finite, a union splits infiniteness to one side, and a degenerate interval is empty.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.infinite_contains_interval_core2 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (A : Set (Power R 1)) (hDef : FiniteUnionOfPointsAndIntervals A) (hInf : Set.Infinite A) :
    exists (a : Endpoint R), exists (b : Endpoint R), Endpoint.lt a b /\ forall (x : Power R 1), openInterval a b x -> A x := by sorry
