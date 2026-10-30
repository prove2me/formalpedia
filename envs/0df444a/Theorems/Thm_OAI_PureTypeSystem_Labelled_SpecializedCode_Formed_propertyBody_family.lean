-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_propertyBody_family
-- name    : OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:03:43.058767+00:00
-- url     : https://prove2.me/theorems/091fbd51-a50c-4d10-a377-5897122cae76
-- title:
--   OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family` of [lean/OAI/Computability/TypeSystem/Specialization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Specialization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`):
--
--   ```lean
--   theorem propertyBody_family (t : Fin 7) : L.Family B.predType (B.propertyBody L.code KY.code KP.code t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.QuantifierRoute`, `OAI.PureTypeSystem.Labelled.SpecializedCode`, `OAI.PureTypeSystem.Labelled.LogicSetup.Family`, `OAI.PureTypeSystem.Labelled.LogicSetup.code`, `OAI.PureTypeSystem.Labelled.QuantifierRoute.code`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.predType` and `OAI.PureTypeSystem.Labelled.SpecializedCode.propertyBody` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proofs of `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_witness_intro`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.delta_congr`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.delta_valid`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_diagonalQ_elim`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_classes_witness_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_congr`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_to_tagged`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_witness_elim`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.goodBody_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.induction_builder`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_congr`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_validStep`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_negative_induction`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_observation_equivalence`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_comparison`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_evaluation`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_left_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_left_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_pair_right_equivalent`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_right_forward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_part_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_part_propertyG`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_positive_shift`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_positive_shift_step`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_respStep`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_probe_response`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qBody_family`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qConsequence_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_qStep_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_queries_family`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relational_bottom`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_R_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_R_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_left`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_pred_compare`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_pred_compare_at`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responsePair_pred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_right`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_evaluation`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_extensional`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePred_typed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responseProbe_compare`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_response_elim`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.sb_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_sb_law`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_evaluation`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_exact`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_respect`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shiftPred_typed`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shift_compare_at`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shift_induction`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.shift_predecessor`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.union_at_witness`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_wfQ_imp` and `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.wfQ_step` of this split import it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Specialization.lean (declaration OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyBody_family)

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000

section

attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode

variable (B : SpecializedCode S)

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem propertyBody_family (t : Fin 7) : L.Family B.predType (B.propertyBody L.code KY.code KP.code t) := by
  sorry

end Formed
end SpecializedCode
end PureTypeSystem.Labelled

end OAI
end
