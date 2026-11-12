-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_raw_joint_shape_score_integrable
-- name    : OAI.IsingPerceptron.raw_joint_shape_score_integrable
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T05:57:49.760124+00:00
-- url     : https://prove2.me/theorems/513c6cc0-8586-4521-92a3-795575d07b11
-- title:
--   OAI.IsingPerceptron.raw_joint_shape_score_integrable: intermediate lemma from OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.InvariantIsing.gaussianPattern_ground_limit_unconditional`, `OAI.InvariantIsing.gaussianPattern_norm_limits_unconditional`, `OAI.InvariantIsing.gaussianPattern_pressure_limit_unconditional`, `OAI.InvariantIsing.ground_state_limit_unconditional`, `OAI.InvariantIsing.limiting_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.limiting_wasserstein_field_pressure_of_extreme_limits_unconditional`, `OAI.InvariantIsing.positive_temperature_pressure_unconditional`, `OAI.InvariantIsing.random_field_pressure_tendsto_ae_unconditional`, `OAI.InvariantIsing.random_pressure_limit_unconditional`, `OAI.InvariantIsing.random_pressure_tendsto_ae_unconditional` and `OAI.InvariantIsing.random_pressure_tendsto_in_measure_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *All-temperature pressure for orthogonally invariant Ising spin glasses*, OpenAI Math Release, September 25, 2026, result family 234, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.IsingPerceptron.raw_joint_shape_score_integrable` of [lean/OAI/Probability/IsingPerceptron/JointShapes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/JointShapes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.IsingPerceptron`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators Topology ENNReal NNReal`):
--
--   ```lean
--   lemma raw_joint_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
--       (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
--       Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*
--         cylinderField (leafLevelCoefficients n d (p.2 0)) p.1.2) (rawLabelJoint n b d t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.IsingPerceptron.CascadeExponents`, `OAI.IsingPerceptron.LabeledLeaf`, `OAI.IsingPerceptron.LabeledTree`, `OAI.IsingPerceptron.PrefixPattern`, `OAI.IsingPerceptron.cylinderField`, `OAI.IsingPerceptron.labelPrefixPattern`, `OAI.IsingPerceptron.labeledLeafMeasurableSpace`, `OAI.IsingPerceptron.labeledTreeMeasurableSpace`, `OAI.IsingPerceptron.leafLevelCoefficients` and `OAI.IsingPerceptron.rawLabelJoint` (definitions bundle `OAIQ4Ip000` of this split).
--
--   **Used by.** The proofs of `OAI.InvariantIsing.field_vector_depth_pair_evaluation`, `OAI.InvariantIsing.field_vector_spin_pair_evaluation`, `OAI.InvariantIsing.restricted_field_depth_pair_evaluation` and `OAI.InvariantIsing.restricted_field_spin_pair_evaluation` of this split import it.
-- source:
--   OpenAI, All-temperature pressure for orthogonally invariant Ising spin glasses, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 234; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/IsingPerceptron/JointShapes.lean (declaration OAI.IsingPerceptron.raw_joint_shape_score_integrable)

import Mathlib
import Definitions.Def_OAIQ4Ip000

section

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

lemma raw_joint_shape_score_integrable (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (d : Fin n) (t : ℝ) (D : PrefixPattern n r → ℝ) :
    Integrable (fun p => D (labelPrefixPattern n r (fun i => p.2 i))*
      cylinderField (leafLevelCoefficients n d (p.2 0)) p.1.2) (rawLabelJoint n b d t) := by
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

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical

end

end OAI
end
