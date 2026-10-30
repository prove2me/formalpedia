-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_good_forward
-- name    : OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:59:41.969132+00:00
-- url     : https://prove2.me/theorems/98964567-1862-45c1-b027-3c0bb349adeb
-- title:
--   OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward` of [lean/OAI/Computability/TypeSystem/Equivalence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Equivalence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`):
--
--   ```lean
--   theorem good_forward {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
--       (hg : Proves P Γ γ (B.good L.code KY.code KP.code v)) :
--       Proves P Γ γ (B.propertyG L.code KY.code KP.code v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.HasType`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.Proves`, `OAI.PureTypeSystem.Labelled.QuantifierRoute`, `OAI.PureTypeSystem.Labelled.SpecializedCode`, `OAI.PureTypeSystem.Labelled.WellModed`, `OAI.PureTypeSystem.Labelled.LogicSetup.code`, `OAI.PureTypeSystem.Labelled.QuantifierRoute.code`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.good`, `OAI.PureTypeSystem.Labelled.SpecializedCode.predType` and `OAI.PureTypeSystem.Labelled.SpecializedCode.propertyG` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proofs of `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_witness_elim`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_observation_equivalence`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_part_propertyG`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.relation_backward` and `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_round_relation` of this split import it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Equivalence.lean (declaration OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_forward)

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

theorem good_forward {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hg : Proves P Γ γ (B.good L.code KY.code KP.code v)) :
    Proves P Γ γ (B.propertyG L.code KY.code KP.code v) := by
  sorry

end Formed
end SpecializedCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end
