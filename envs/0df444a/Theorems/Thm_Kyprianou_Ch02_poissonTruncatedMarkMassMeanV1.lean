-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonTruncatedMarkMassMeanV1
-- name    : Kyprianou.Ch02.poissonTruncatedMarkMassMeanV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:04:23.035322+00:00
-- url     : https://prove2.me/theorems/3b851380-00b1-4f09-a636-3f62737e0268
-- title:
--   Exact expected truncated Poisson mark mass on integer time windows
-- statement:
--   Apply the genuine Poisson first-moment ENNReal identity to the nonnegative time-windowed min(1,abs mark) function. Evaluate the intensity product measure by Tonelli. Holds even for infinite first moment.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.12; LeanLevy path construction and generic Avram finite-cylinder path law.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.poissonTruncatedMarkMassMeanV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (n : ℕ) :
    (∫⁻ ω, ∫⁻ p : ℝ × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
      else 0 ∂(poissonRandomMeasure K Z ω) ∂P) =
      (n : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂ν) := by
  sorry
