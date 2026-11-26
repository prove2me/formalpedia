-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ApproxEnvelopeV10
-- name    : Kyprianou.Ch04.exercise41ApproxEnvelopeV10
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:41:20.45287+00:00
-- url     : https://prove2.me/theorems/94da3794-0bf5-5173-8cca-413abb41a079
-- title:
--   Compact BV path turns local derivative bounds into integrable drift and summable jump envelopes
-- statement:
--   Compact BV path turns local derivative bounds into integrable drift and summable jump envelopes
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

theorem Kyprianou.Ch04.exercise41ApproxEnvelopeV10
    {Ω : Type}
    (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (hSum : ∀ t : NNReal,
      Summable (fun s : Ioc (0 : NNReal) t => |X s w - Xleft s w|))
    (g : ℕ → ℝ → ℝ) (G D : ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (G x)))
    (hD : ∀ x, Tendsto (fun n => deriv (g n) x) atTop (𝓝 (D x)))
    (hBound : ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 ≤ K ∧
      ∀ n x, |x| ≤ R → ‖deriv (g n) x‖ ≤ K)
    (t : NNReal) :
    let μ := (volume : Measure ℝ).restrict (Icc 0 (t : ℝ))
    ∃ (K : ℝ → ℝ) (B : Ioc (0 : NNReal) t → ℝ),
      (∀ n, AEStronglyMeasurable (fun s => deriv (g n) (X s.toNNReal w)) μ) ∧
      Integrable K μ ∧
      (∀ n, ∀ᵐ s ∂μ, ‖deriv (g n) (X s.toNNReal w)‖ ≤ K s) ∧
      (∀ᵐ s ∂μ, Tendsto (fun n => deriv (g n) (X s.toNNReal w)) atTop
        (𝓝 (D (X s.toNNReal w)))) ∧
      Summable B ∧
      (∀ᶠ n in atTop, ∀ k : Ioc (0 : NNReal) t,
        ‖g n (X k w) - g n (Xleft k w)‖ ≤ B k) ∧
      Summable (fun k : Ioc (0 : NNReal) t => ‖G (X k w) - G (Xleft k w)‖) := by
  sorry
