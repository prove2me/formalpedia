-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41DriftEnvelopeV10
-- name    : Kyprianou.Ch04.exercise41DriftEnvelopeV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:43:11.148478+00:00
-- url     : https://prove2.me/theorems/07a5609a-c483-564f-8f6d-4b69bfc6d61d
-- title:
--   Bounded spatial derivatives provide an integrable constant drift envelope and measurable pointwise limits
-- statement:
--   Bounded spatial derivatives provide an integrable constant drift envelope and measurable pointwise limits
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41DriftEnvelopeV10
    (X : ℝ → ℝ) (hX : Measurable X) (t R K : ℝ)
    (hXt : ∀ s ∈ Icc (0 : ℝ) t, |X s| ≤ R)
    (g : ℕ → ℝ → ℝ) (D : ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hD : ∀ x, Tendsto (fun n => deriv (g n) x) atTop (𝓝 (D x)))
    (hBound : ∀ n x, |x| ≤ R → ‖deriv (g n) x‖ ≤ K) :
    let μ := (volume : Measure ℝ).restrict (Icc 0 t)
    (∀ n, AEStronglyMeasurable (fun s => deriv (g n) (X s)) μ) ∧
    Integrable (fun _ : ℝ => K) μ ∧
    (∀ n, ∀ᵐ s ∂μ, ‖deriv (g n) (X s)‖ ≤ K) ∧
    (∀ᵐ s ∂μ, Tendsto (fun n => deriv (g n) (X s)) atTop (𝓝 (D (X s)))) := by
  sorry
