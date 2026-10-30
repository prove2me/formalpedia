-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_propertyG_roundRespect
-- name    : OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyG_roundRespect
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:03:39.856538+00:00
-- url     : https://prove2.me/theorems/cc27e221-ab17-4be2-be54-f9909bf6e5dd
-- title:
--   OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyG_roundRespect: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyG_roundRespect` of [lean/OAI/Computability/TypeSystem/Equivalence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Equivalence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`):
--
--   ```lean
--   theorem propertyG_roundRespect {v : Expr S}
--       (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
--       (hp : Proves P Γ γ (B.propertyG L.code KY.code KP.code v)) :
--       Proves P Γ γ (B.relational.channel.roundRespect L.code KY.code B.baseType v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.HasType`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.Proves`, `OAI.PureTypeSystem.Labelled.QuantifierRoute`, `OAI.PureTypeSystem.Labelled.SpecializedCode`, `OAI.PureTypeSystem.Labelled.WellModed`, `OAI.PureTypeSystem.Labelled.ChannelCode.roundRespect`, `OAI.PureTypeSystem.Labelled.LogicSetup.code`, `OAI.PureTypeSystem.Labelled.QuantifierRoute.code`, `OAI.PureTypeSystem.Labelled.RelationalCode.channel`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.baseType`, `OAI.PureTypeSystem.Labelled.SpecializedCode.predType`, `OAI.PureTypeSystem.Labelled.SpecializedCode.propertyG` and `OAI.PureTypeSystem.Labelled.SpecializedCode.relational` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proof of `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward` of this split imports it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Equivalence.lean (declaration OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.propertyG_roundRespect)

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

namespace SpecializedCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem propertyG_roundRespect {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hp : Proves P Γ γ (B.propertyG L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.channel.roundRespect L.code KY.code B.baseType v) := by
  sorry
end SpecializedCode.Formed

end

universe u
end PureTypeSystem.Labelled

end OAI
end
