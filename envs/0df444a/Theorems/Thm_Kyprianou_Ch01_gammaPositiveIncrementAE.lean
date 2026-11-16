-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaPositiveIncrementAE
-- name    : Kyprianou.Ch01.gammaPositiveIncrementAE
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T19:52:06.232579+00:00
-- url     : https://prove2.me/theorems/92174f0a-2c7a-430a-8a36-53cebd0e0721
-- title:
--   Gamma Lévy process increments are almost surely strictly positive over each positive time interval
-- statement:
--   Strict positivity at every fixed positive gamma time, together with the Lévy stationary-increments law, implies X_t−X_s>0 almost surely for each fixed s<t. An identically distributed process increment has the same half-line null probability as the original positive-duration marginal. The fixed-time positivity theorem is a separately published Chapter 1 child. This theorem has exactly the stochastic and Laplace hypotheses inherited from the parent gamma-path assertion.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.4, gamma Lévy subordinator strict path increase; Lévy stationary increments from Definition 1.2.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaPositiveIncrementAE
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ)))
    (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ ω ∂P, X s ω < X t ω := by sorry
