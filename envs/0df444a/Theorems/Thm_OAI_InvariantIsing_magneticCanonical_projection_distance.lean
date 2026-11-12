-- Prove2me | Theorems.Thm_OAI_InvariantIsing_magneticCanonical_projection_distance
-- name    : OAI.InvariantIsing.magneticCanonical_projection_distance
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:39:17.336077+00:00
-- url     : https://prove2.me/theorems/58f2eb27-68ea-4f51-ab93-d8e9553bfb5c
-- title:
--   OAI.InvariantIsing.magneticCanonical_projection_distance: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.magneticCanonical_projection_distance` of [lean/OAI/Probability/InvariantIsing/Magnetic/MagneticCanonicalSpin.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticCanonicalSpin.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   theorem magneticCanonical_projection_distance {N : ℕ} {A : Type*}
--       [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
--       (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
--       (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
--       (h : FieldStep) :
--       (∫ σ : Spin N, (hammingDist σ (spinGroupProjection group k hk σ) : ℝ)
--         ∂Measure.pi (fun i => fieldCanonicalSpinLaw h (magneticBias h (m (group i))))) ≤
--           ∑ a, Real.sqrt (spinGroupSize group a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.spinGroupSize` (definitions bundle `OAIQ258002` of this split); `OAI.InvariantIsing.spinGroupProjection` (definitions bundle `OAIQ258004` of this split); `OAI.InvariantIsing.fieldCanonicalSpinLaw` and `OAI.InvariantIsing.magneticBias` (definitions bundle `OAIQ258005` of this split); `OAI.InvariantIsing.FieldStep` and `OAI.InvariantIsing.Spin` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.magneticBlockPath_l1_tendsto` and `OAI.InvariantIsing.magnetic_affine_increment_eventually_lower` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Magnetic/MagneticCanonicalSpin.lean (declaration OAI.InvariantIsing.magneticCanonical_projection_distance)

import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.Variance
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005

section

attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.fieldCanonicalEndpointLaw_probability _root_.OAI.InvariantIsing.fieldCanonicalVectorLaw_probability _root_.OAI.InvariantIsing.fieldVectorCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.fieldVectorPairSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorSpinKernel_markov _root_.OAI.InvariantIsing.fieldVectorTailSpinKernel_markov _root_.OAI.InvariantIsing.priorFrozenReference_probability _root_.OAI.InvariantIsing.priorNamespacedReference_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.restrictedLevelSpinPair_probability _root_.OAI.InvariantIsing.restrictedPairEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedPairSpinKernel_markov _root_.OAI.InvariantIsing.restrictedRotationProbability_probability _root_.OAI.InvariantIsing.restrictedTailEndpointKernel_markov _root_.OAI.InvariantIsing.restrictedTailSpinKernel_markov _root_.OAI.InvariantIsing.restrictedZeroTreePrior_probability _root_.OAI.InvariantIsing.spinPriorFrozenReference_probability _root_.OAI.InvariantIsing.spinPriorLabeledReference_probability _root_.OAI.InvariantIsing.spinPriorNamespacedReference_probability _root_.OAI.InvariantIsing.tensorFrozenReference_probability _root_.OAI.InvariantIsing.tensorNamespacedReference_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

theorem magneticCanonical_projection_distance {N : ℕ} {A : Type*}
    [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (m : A → ℝ) (hm : ∀ a, |m a| < 1)
    (hcount : ∀ a, (k a : ℝ) = (spinGroupSize group a : ℝ) * ((1 + m a) / 2))
    (h : FieldStep) :
    (∫ σ : Spin N, (hammingDist σ (spinGroupProjection group k hk σ) : ℝ)
      ∂Measure.pi (fun i => fieldCanonicalSpinLaw h (magneticBias h (m (group i))))) ≤
        ∑ a, Real.sqrt (spinGroupSize group a) := by
  sorry

end InvariantIsing

end

end OAI
end
