-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_probe_exact
-- name    : OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:02:24.354998+00:00
-- url     : https://prove2.me/theorems/a4347a2e-4460-46d0-ab79-9f4bbce50335
-- title:
--   OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact` of [lean/OAI/Computability/TypeSystem/Response.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Response.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`):
--
--   ```lean
--   theorem probe_exact {i y : Expr S}
--       (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
--       (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
--       (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
--       Equivalent P Γ γ (B.diamond L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y)
--         (B.relational.channel.eval B.relational.probe.carrier i (B.lift L.code KY.code KP.code y))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.Equivalent`, `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.HasType`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.Proves`, `OAI.PureTypeSystem.Labelled.QuantifierRoute`, `OAI.PureTypeSystem.Labelled.SpecializedCode`, `OAI.PureTypeSystem.Labelled.WellModed`, `OAI.PureTypeSystem.Labelled.ChannelCode.eval`, `OAI.PureTypeSystem.Labelled.LogicSetup.code`, `OAI.PureTypeSystem.Labelled.ProbeCode.carrier`, `OAI.PureTypeSystem.Labelled.QuantifierRoute.code`, `OAI.PureTypeSystem.Labelled.RelationalCode.channel`, `OAI.PureTypeSystem.Labelled.RelationalCode.extensional`, `OAI.PureTypeSystem.Labelled.RelationalCode`, `OAI.PureTypeSystem.Labelled.RelationalCode.probeFor`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.diamond`, `OAI.PureTypeSystem.Labelled.SpecializedCode.lift`, `OAI.PureTypeSystem.Labelled.SpecializedCode.relational`, `OAI.PureTypeSystem.Labelled.SpecializedCode.xPredType` and `OAI.PureTypeSystem.Labelled.SpecializedCode.yType` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proofs of `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.induction_builder`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_respStep`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.shift_predecessor` and `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.wfQ_step` of this split import it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Response.lean (declaration OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact)

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

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem probe_exact {i y : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Equivalent P Γ γ (B.diamond L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y)
      (B.relational.channel.eval B.relational.probe.carrier i (B.lift L.code KY.code KP.code y)) := by
  sorry

end

end SpecializedCode.Formed
end PureTypeSystem.Labelled

end OAI
end
