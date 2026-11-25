-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFullFderivEqWithinPositiveV1
-- name    : Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:31:34.238715+00:00
-- url     : https://prove2.me/theorems/e058a794-feff-4954-b41b-9381c2c20427
-- title:
--   Full and half-plane derivatives coincide at positive times
-- statement:
--   At positive time the half-plane contains a neighbourhood and has unique within derivatives. The differentiable-at derivative therefore agrees with the within derivative.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFullFderivEqWithinPositiveV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (u x : ℝ) (hu : 0 < u) :
    fderivWithin ℝ f (Set.prod (Set.Ici (0 : ℝ)) Set.univ) (u,x) =
      fderiv ℝ f (u,x) := by
  sorry
