-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_capped_recTopCoe_integral_limit
-- name    : Kyprianou.Ch08.StageB.p2m810_capped_recTopCoe_integral_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:03:09.10356+00:00
-- url     : https://prove2.me/theorems/33a129d0-7be3-4f4f-9281-373035cfc823
-- title:
--   For each finite clock the capped integrand eventually agrees with the original payoff. Infinite clocks contribute zero. Dominated convergence passes to the full expectation.
-- statement:
--   For each finite clock the capped integrand eventually agrees with the original payoff. Infinite clocks contribute zero. Dominated convergence passes to the full expectation.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii)

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_capped_recTopCoe_integral_limit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → WithTop ℝ≥0) (f : ℝ≥0 → Ω → ℝ)
    (hb : ∀ t ω, 0 ≤ f t ω ∧ f t ω ≤ 1)
    (hm : ∀ n : ℕ, Measurable (fun ω =>
      if τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) then
        f (WithTop.untopD 0 (min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0))) ω else 0)) :
    Tendsto (fun n : ℕ => ∫ ω,
      if τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) then
        f (WithTop.untopD 0 (min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0))) ω else 0 ∂P)
      atTop (𝓝 (∫ ω, WithTop.recTopCoe (C := fun _ => ℝ) 0
        (fun t => f t ω) (τ ω) ∂P)) := by
  sorry
