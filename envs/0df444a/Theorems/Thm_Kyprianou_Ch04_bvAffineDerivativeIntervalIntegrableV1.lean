-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvAffineDerivativeIntervalIntegrableV1
-- name    : Kyprianou.Ch04.bvAffineDerivativeIntervalIntegrableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:04:33.829561+00:00
-- url     : https://prove2.me/theorems/bfdc3feb-eafc-4f41-a0f3-e740b54d1cc9
-- title:
--   Interval integrability of a derivative evaluated along an affine segment
-- statement:
--   Continuity of the within-domain derivative on the half-plane gives interval integrability along an affine segment. The full derivative agrees at every interior time, and endpoints have zero Lebesgue measure.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; deterministic finite-jump telescoping.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvAffineDerivativeIntervalIntegrableV1
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (a d l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (v : ℝ × ℝ) :
    IntervalIntegrable (fun u => fderiv ℝ f (u, a + d * u) v) volume l r := by
  sorry
