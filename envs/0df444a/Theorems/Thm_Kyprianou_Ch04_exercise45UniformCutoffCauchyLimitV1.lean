-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45UniformCutoffCauchyLimitV1
-- name    : Kyprianou.Ch04.exercise45UniformCutoffCauchyLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:36:11.469279+00:00
-- url     : https://prove2.me/theorems/8d70a69f-bd18-4330-80c7-baa1f4b024d9
-- title:
--   Uniform real-cutoff Cauchy estimates give a uniform path limit
-- statement:
--   Use completeness at each time along a positive sequence converging to zero. Pass the uniform Cauchy inequality to that limit, then use the within-neighbourhood criterion.
-- source:
--   Kyprianou (2006), Exercise 4.5 proof auxiliary

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45UniformCutoffCauchyLimitV1
    (A : ℝ → NNReal → ℝ) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (nhds 0))
    (hC : ∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
      ∀ r q : ℝ, 0 < r → r < a → 0 < q → q < a →
        ∀ t ≤ T, |A r t - A q t| < δ) :
    ∃ Z : NNReal → ℝ,
      (∀ T : NNReal, ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧
        ∀ r : ℝ, 0 < r → r < a → ∀ t ≤ T, |A r t - Z t| ≤ δ) ∧
      (∀ t : NNReal, Tendsto (fun r : ℝ => A r t)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Z t))) := by sorry
