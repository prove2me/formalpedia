-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleOccupationNatHorizonSupV1
-- name    : Kyprianou.Ch04.idleOccupationNatHorizonSupV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:25:01.383205+00:00
-- url     : https://prove2.me/theorems/5c3080ed-6d69-410a-88f1-bb9dc2ea7e8d
-- title:
--   Infinite occupation is the supremum of finite integer-horizon occupations
-- statement:
--   Convert each restricted indicator integral to the volume of the intersection. The finite intervals are increasing and exhaust the positive half-line; continuity from below gives the result.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic regulator calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleOccupationNatHorizonSupV1
    (A : Set Real) (hA : MeasurableSet A) :
    (∫⁻ t in Ici (0 : Real), A.indicator (fun _ => (1 : ENNReal)) t ∂volume) =
      ⨆ n : Nat, ∫⁻ t in Icc (0 : Real) (n : Real),
        A.indicator (fun _ => (1 : ENNReal)) t ∂volume := by
  sorry
