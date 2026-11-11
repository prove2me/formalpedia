-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_normalJointPast_product_identification
-- name    : OAI.DirectionalTransience.normalJointPast_product_identification
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:45:50.939522+00:00
-- url     : https://prove2.me/theorems/d1d509ef-4a0b-4c3b-9488-6ce75e768bd4
-- title:
--   OAI.DirectionalTransience.normalJointPast_product_identification: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.normalJointPast_product_identification` of [lean/OAI/Probability/Ballisticity/Walk/JointPathIndependence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Walk/JointPathIndependence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction`):
--
--   ```lean
--   lemma normalJointPast_product_identification (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
--       (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
--       (hcross : SeparatedCrossBound μ A K)
--       (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
--       (hzero : ∀ᵐ P ∂μ,P.1 0=0 ∧ P.2 0=0) :
--       μ=(μ.map Prod.fst).prod (μ.map Prod.snd)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.NormalJointPast`, `OAI.DirectionalTransience.RealPathPair`, `OAI.DirectionalTransience.SeparatedCrossBound` and `OAI.DirectionalTransience.continuousPathMeasurableSpace` (definitions bundle `OAIQ242Bal001` of this split).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.shared_pair_path_limit` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Walk/JointPathIndependence.lean (declaration OAI.DirectionalTransience.normalJointPast_product_identification)

import Mathlib
import Definitions.Def_OAIQ242Bal001

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_product_identification (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hcross : SeparatedCrossBound μ A K)
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
    (hzero : ∀ᵐ P ∂μ,P.1 0=0 ∧ P.2 0=0) :
    μ=(μ.map Prod.fst).prod (μ.map Prod.snd) := by
  sorry

end DirectionalTransience

end

end

end OAI
end
