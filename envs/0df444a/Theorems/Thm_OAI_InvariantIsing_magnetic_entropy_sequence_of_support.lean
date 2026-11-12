-- Prove2me | Theorems.Thm_OAI_InvariantIsing_magnetic_entropy_sequence_of_support
-- name    : OAI.InvariantIsing.magnetic_entropy_sequence_of_support
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:39:58.316568+00:00
-- url     : https://prove2.me/theorems/03bd2389-69b3-4715-8db2-0abcbb2f4f4a
-- title:
--   OAI.InvariantIsing.magnetic_entropy_sequence_of_support: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.magnetic_entropy_sequence_of_support` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticEntropySequence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticEntropySequence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem magnetic_entropy_sequence_of_support {A : Type*} [Fintype A]
--       (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
--       (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (h : ℕ → FieldStep)
--       {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
--       (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
--         (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s * (fieldFunction k s - fieldFunction (h n) s)
--           ∂pathMeasure) / 2)
--       (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s - p s| ∂pathMeasure)
--         atTop (𝓝 0)) :
--       magneticEntropyFunctional γ mag p ≠ ⊤ ∧
--       Tendsto (fun n => magneticGroupValue γ mag (h n) + fieldPairing p (h n) / 2)
--         atTop (𝓝 (magneticEntropyFunctional γ mag p).toReal)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.magneticGroupPath` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.FieldStep`, `OAI.InvariantIsing.OverlapPath`, `OAI.InvariantIsing.fieldFunction`, `OAI.InvariantIsing.fieldPairing`, `OAI.InvariantIsing.magneticEntropyFunctional`, `OAI.InvariantIsing.magneticGroupValue` and `OAI.InvariantIsing.pathMeasure` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.magnetic_entropy_trial_eventually_lower` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticEntropySequence.lean (declaration OAI.InvariantIsing.magnetic_entropy_sequence_of_support)

import Mathlib
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Sort
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Order.Compact
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology

namespace InvariantIsing

theorem magnetic_entropy_sequence_of_support {A : Type*} [Fintype A]
    (γ mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a = 1)
    (hmag : ∀ a, |mag a| ≤ 1) (p : OverlapPath) (h : ℕ → FieldStep)
    {C : ℝ} (hC : ∀ n, (h n).height (Fin.last (h n).depth) ≤ C)
    (hsupport : ∀ n k, magneticGroupValue γ mag k ≤ magneticGroupValue γ mag (h n) -
      (∫ s, magneticGroupPath γ mag hγ hγsum (h n) s * (fieldFunction k s - fieldFunction (h n) s)
        ∂pathMeasure) / 2)
    (hself : Tendsto (fun n => ∫ s, |magneticGroupPath γ mag hγ hγsum (h n) s - p s| ∂pathMeasure)
      atTop (𝓝 0)) :
    magneticEntropyFunctional γ mag p ≠ ⊤ ∧
    Tendsto (fun n => magneticGroupValue γ mag (h n) + fieldPairing p (h n) / 2)
      atTop (𝓝 (magneticEntropyFunctional γ mag p).toReal) := by
  sorry

end InvariantIsing

end

end OAI
end
