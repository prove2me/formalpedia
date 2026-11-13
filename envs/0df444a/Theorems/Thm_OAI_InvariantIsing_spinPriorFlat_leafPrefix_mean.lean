-- Prove2me | Theorems.Thm_OAI_InvariantIsing_spinPriorFlat_leafPrefix_mean
-- name    : OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T05:32:30.867195+00:00
-- url     : https://prove2.me/theorems/44e25cb9-f0bf-4ccb-bc22-ec775be854b2
-- title:
--   OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean` of [lean/OAI/Probability/InvariantIsing/Fields/SpinPriorLeafTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorLeafTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.InvariantIsing`, with `open MeasureTheory ProbabilityTheory IsingPerceptron`, `open scoped Topology NNReal`):
--
--   ```lean
--   lemma spinPriorFlat_leafPrefix_mean {N m k : ℕ} (hN : 0 < N)
--       (π : Measure (Spin N)) [IsProbabilityMeasure π]
--       (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
--       (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
--       (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
--       (hb : CascadeExponents n b) (d : Fin n) :
--       (∫ p : LabeledTree n × (ℕ → ℝ),
--         referenceReplicaMean (labeledSpinReference n π p.1)
--           (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
--             cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2)
--           (tensorLeafPrefixTest d)
--         ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) = 1 - b d
--   ```
--
--   **Definitions.** The statement is written with `OAI.InvariantIsing.SpinTensorIndex` (definitions bundle `OAIQ258000` of this split); `OAI.InvariantIsing.tensorLeafCoefficients` (definitions bundle `OAIQ258003` of this split); `OAI.InvariantIsing.tensorLeafPrefixTest` (definitions bundle `OAIQ258004` of this split); `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.cylinderField`, `OAI.IsingPerceptron.gaussianCoordinates`, `OAI.IsingPerceptron.labeledCascadeLaw`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledSpinReference`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace` and `OAI.IsingPerceptron.referenceReplicaMean` (definitions bundle `OAIQ4Ip000` of this split); `OAI.InvariantIsing.Rotation`, `OAI.InvariantIsing.Spin`, `OAI.InvariantIsing.fieldEnergy` and `OAI.InvariantIsing.rotatedEnergy` (the published bundle `Def_InvariantIsing`).
--
--   **Used by.** The proof of `OAI.InvariantIsing.spinPriorContact_limit_tail_order` of this split imports it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/InvariantIsing/Fields/SpinPriorLeafTail.lean (declaration OAI.InvariantIsing.spinPriorFlat_leafPrefix_mean)

import Mathlib
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Definitions.Def_OAIQ258004

section

attribute [-instance] _root_.OAI.InvariantIsing.cavityHaarSpinPriorKernel_isMarkov _root_.OAI.InvariantIsing.cavityLabeledDisorderLaw_probability _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov _root_.OAI.InvariantIsing.cavityLabeledPriorKernel_markov _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.InvariantIsing.cavityRootedFullGibbs_markov _root_.OAI.InvariantIsing.cavityRotationProbability_probability _root_.OAI.InvariantIsing.priorSpinLeafPairResidualKernel_markov _root_.OAI.InvariantIsing.vectorLabeledTerminalLaw_probability _root_.OAI.InvariantIsing.vectorTerminalCoordinateLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Topology NNReal
namespace InvariantIsing

lemma spinPriorFlat_leafPrefix_mean {N m k : ℕ} (hN : 0 < N)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (d : Fin n) :
    (∫ p : LabeledTree n × (ℕ → ℝ),
      referenceReplicaMean (labeledSpinReference n π p.1)
        (fun x => rotatedEnergy eig U x.1 + fieldEnergy c x.1 +
          cylinderField (tensorLeafCoefficients U I degree amp n (fun i => v i) x) p.2)
        (tensorLeafPrefixTest d)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) = 1 - b d := by
  sorry

end InvariantIsing

end

end OAI
end
