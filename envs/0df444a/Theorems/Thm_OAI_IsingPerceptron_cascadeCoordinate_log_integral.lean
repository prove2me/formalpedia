-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_cascadeCoordinate_log_integral
-- name    : OAI.IsingPerceptron.cascadeCoordinate_log_integral
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:51.565699+00:00
-- url     : https://prove2.me/theorems/2fc1d6e2-d3ff-4c6f-8bc2-c27431fcbd21
-- title:
--   OAI.IsingPerceptron.cascadeCoordinate_log_integral: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.cascadeCoordinate_log_integral` of [lean/OAI/Probability/IsingPerceptron/EnrichedCGF.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/EnrichedCGF.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`):
--
--   ```lean
--   lemma cascadeCoordinate_log_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
--       (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
--       (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
--       Integrable (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
--         ∂labeledSpinReference n ν p.1)) (cascadeCoordinateLaw n b μ) ∧
--       (∫ p, Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
--         ∂labeledSpinReference n ν p.1) ∂cascadeCoordinateLaw n b μ) = energyRecursion n b μ ν H
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.cascadeCoordinateEnergy` and `OAI.IsingPerceptron.cascadeCoordinateLaw` (definitions bundle `OAIQ258002` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.ExponentialNormMoments`, `OAI.IsingPerceptron.ForestVertex`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.energyRecursion`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledSpinReference` and `OAI.IsingPerceptron.labeledTreeMeasurableSpace` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean` and `OAI.InvariantIsing.tensorFlat_leafPrefix_mean` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/EnrichedCGF.lean (declaration OAI.IsingPerceptron.cascadeCoordinate_log_integral)

import Mathlib
import Definitions.Def_OAIQ258002

section

attribute [-instance] _root_.OAI.InvariantIsing.vectorTerminalNoiseLaw_probability _root_.OAI.IsingPerceptron.cascadeReplicaLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.labeledWeightedLeafLaw_probability _root_.OAI.IsingPerceptron.rawLabelBase_probability _root_.OAI.IsingPerceptron.rawLabelJoint_probability _root_.OAI.IsingPerceptron.rawLeafGibbs_probability _root_.OAI.IsingPerceptron.retainedLabelBase_probability _root_.OAI.IsingPerceptron.retainedLabelJoint_probability _root_.OAI.IsingPerceptron.retainedLabelLeafLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron
variable {I : Type} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma cascadeCoordinate_log_integral (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (H : I → ℝ) :
    Integrable (fun p => Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
      ∂labeledSpinReference n ν p.1)) (cascadeCoordinateLaw n b μ) ∧
    (∫ p, Real.log (∫ s, Real.exp (cascadeCoordinateEnergy n H p s)
      ∂labeledSpinReference n ν p.1) ∂cascadeCoordinateLaw n b μ) = energyRecursion n b μ ν H := by
  sorry

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end
