-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyGridCharDefectLinearV1
-- name    : Kyprianou.Ch02.levyGridCharDefectLinearV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T00:18:47.291656+00:00
-- url     : https://prove2.me/theorems/e1783da0-9b84-4704-9792-77806f9eff5d
-- title:
--   Scaled characteristic deficits converge to the negative real exponent
-- statement:
--   Apply the punctured-neighbourhood derivative limit for t⁻¹(1-exp(t z)).re along t=1/(n+1).
-- source:
--   Kyprianou (2006), Lemma 2.12

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.levyGridCharDefectLinearV1
    (z : ℂ) (C : ℝ)
    (h : ∀ n : ℕ, ((n : ℝ)+1) *
      (1 - Complex.exp (((((n : ℝ)+1)⁻¹) : ℂ) * z)).re ≤ C) :
    -z.re ≤ C := by sorry
