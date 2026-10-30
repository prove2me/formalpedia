-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_parameter_query
-- name    : OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:01:02.56906+00:00
-- url     : https://prove2.me/theorems/5b91860f-8980-4ab3-b2ab-6f15b14fb236
-- title:
--   OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query` of [lean/OAI/Computability/TypeSystem/Specialization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Specialization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`):
--
--   ```lean
--   theorem parameter_query (t : Fin 7) {v : Expr S}
--       (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
--       Equivalent P Γ γ
--         (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
--           (B.parameter L.code KY.code KP.code) v)
--         (B.property L.code KY.code KP.code t v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.Equivalent`, `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.HasType`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.QuantifierRoute`, `OAI.PureTypeSystem.Labelled.SpecializedCode`, `OAI.PureTypeSystem.Labelled.WellModed`, `OAI.PureTypeSystem.Labelled.DoubleCode.query`, `OAI.PureTypeSystem.Labelled.LogicSetup.code`, `OAI.PureTypeSystem.Labelled.ProbeCode.doubled`, `OAI.PureTypeSystem.Labelled.ProbeCode.rawType`, `OAI.PureTypeSystem.Labelled.QuantifierRoute.code`, `OAI.PureTypeSystem.Labelled.RelationalCode`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.parameter`, `OAI.PureTypeSystem.Labelled.SpecializedCode.predType`, `OAI.PureTypeSystem.Labelled.SpecializedCode.property` and `OAI.PureTypeSystem.Labelled.SpecializedCode.relational` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proofs of `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_query`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_congr`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_query`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_witness_elim`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_congr`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_validStep`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_observation_equivalence`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_pair_right_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_responsePair_left`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.sb_equivalent`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_sb_law` and `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.shift_predecessor` of this split import it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Specialization.lean (declaration OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query)

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000

section

attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
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

theorem parameter_query (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ
      (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
        (B.parameter L.code KY.code KP.code) v)
      (B.property L.code KY.code KP.code t v) := by
  sorry
end Formed
end SpecializedCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end
