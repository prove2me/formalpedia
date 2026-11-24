-- Prove2me | Theorems.Thm_Kyprianou_Ch02_poissonTruncatedMarkMassFiniteAEV1
-- name    : Kyprianou.Ch02.poissonTruncatedMarkMassFiniteAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:51:20.960554+00:00
-- url     : https://prove2.me/theorems/97dfd2f5-af8f-41bf-93f2-443a12972371
-- title:
--   Finite first moment gives finite truncated Poisson mark mass on every integer horizon
-- statement:
--   Apply the proved Campbell identity and the finite first moment assumption to obtain an almost surely finite nonnegative integral on each integer horizon. Intersect the countably many conull events.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.12; canonical finite first moment model and equality of real Levy path laws.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
open MeasureTheory ProbabilityTheory Complex Function Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.poissonTruncatedMarkMassFiniteAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod ν) P)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) ν) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫⁻ p : ℝ × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ) then ENNReal.ofReal (min (1 : ℝ) |p.2|)
        else 0 ∂(poissonRandomMeasure K Z ω)) < ⊤ := by
  sorry
