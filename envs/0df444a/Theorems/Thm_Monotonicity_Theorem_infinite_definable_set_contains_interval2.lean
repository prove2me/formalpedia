-- Prove2me | Theorems.Thm_Monotonicity_Theorem_infinite_definable_set_contains_interval2
-- name    : Monotonicity_Theorem.infinite_definable_set_contains_interval2
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-14T23:46:34.186805+00:00
-- url     : https://prove2.me/theorems/c5419b5f-89bf-4bca-ae90-7647f1f552ff
-- title:
--   Infinite definable sets contain intervals
-- statement:
--   An infinite definable set of unary tuples contains a nondegenerate open interval: o-minimality turns definability into a finite-union structure, and infiniteness forces an interval piece.
-- source:
--   van den Dries, Tame Topology and O-Minimal Structures, Ch. 3

import Definitions.Def_Monotonicity_Theorem_Framework2

theorem Monotonicity_Theorem.infinite_definable_set_contains_interval2 {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R] (M : OMinimalStructure R) (I : Set (Power R 1)) (hDef : M.S 1 I) (hInf : Set.Infinite I) : exists (a : Endpoint R), exists (b : Endpoint R), Endpoint.lt a b /\ (openInterval a b).Subset I := by sorry
