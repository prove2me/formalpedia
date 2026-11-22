-- Prove2me | Theorems.Thm_Monotonicity_Theorem_exception_list
-- name    : Monotonicity_Theorem.exception_list
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-09T19:03:19.600395+00:00
-- url     : https://prove2.me/theorems/fd180e3a-1b56-48d5-a6b9-4b2414200a77
-- title:
--   Exception list covering a finite union
-- statement:
--   A finite union of points and intervals admits a finite exception list: every point is either listed or sits in a subinterval fully contained in the set whose finite endpoints are listed.
-- source:
--   Monotonicity theorem Lemma 2 infrastructure

import Definitions.Def_Monotonicity_Theorem_Framework

theorem Monotonicity_Theorem.exception_list {R : Type} (D : DenseLinearOrderNoEndpoints R)
    {A : Set (Power R 1)} (hA : FiniteUnionOfPointsAndIntervals D A) :
    exists E : List R, forall x : Power R 1, A x ->
      Power.coord1 x ∈ E \/
      exists a b : Endpoint R, openInterval D a b x /\
        (forall y : Power R 1, openInterval D a b y -> A y) /\
        (forall v : R, a = Endpoint.finite v -> v ∈ E) /\
        (forall v : R, b = Endpoint.finite v -> v ∈ E) := by sorry
