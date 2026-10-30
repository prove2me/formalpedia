-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_edge_to_tagged
-- name    : OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_to_tagged
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:58:18.845789+00:00
-- url     : https://prove2.me/theorems/db7ad5d8-26c7-4f2a-9426-4bc3c0de41fc
-- title:
--   OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_to_tagged: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_to_tagged` of [lean/OAI/Computability/TypeSystem/Diagonal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Diagonal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`):
--
--   ```lean
--   theorem edge_to_tagged (t : Bool) {y x : Expr S}
--       (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
--       (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
--       (he : Proves P Γ γ (B.edge L.code KY.code KP.code t y (B.observation.tagged L.code (if t then 2 else 1) x))) :
--       Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.HasType`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.Proves`, `OAI.PureTypeSystem.Labelled.QuantifierRoute`, `OAI.PureTypeSystem.Labelled.SpecializedCode`, `OAI.PureTypeSystem.Labelled.WellModed`, `OAI.PureTypeSystem.Labelled.LogicSetup.code`, `OAI.PureTypeSystem.Labelled.ObservationCode.tagged`, `OAI.PureTypeSystem.Labelled.QuantifierRoute.code`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.edge`, `OAI.PureTypeSystem.Labelled.SpecializedCode.relation`, `OAI.PureTypeSystem.Labelled.SpecializedCode.xType` and `OAI.PureTypeSystem.Labelled.SpecializedCode.yType` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proofs of `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_left_equivalent` and `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.pair_right_forward` of this split import it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Diagonal.lean (declaration OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_to_tagged)

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

theorem edge_to_tagged (t : Bool) {y x : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.edge L.code KY.code KP.code t y (B.observation.tagged L.code (if t then 2 else 1) x))) :
    Proves P Γ γ (B.relation L.code KY.code KP.code y (B.observation.tagged L.code 0 x)) := by
  sorry

end

end SpecializedCode.Formed

end PureTypeSystem.Labelled

end OAI
end
