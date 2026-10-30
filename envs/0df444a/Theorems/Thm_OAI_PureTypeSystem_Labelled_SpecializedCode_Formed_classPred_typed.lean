-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_classPred_typed
-- name    : OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.classPred_typed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:56:14.307141+00:00
-- url     : https://prove2.me/theorems/6a8a8c9a-45e4-4a61-a91f-05e76a20c54f
-- title:
--   OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.classPred_typed: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.classPred_typed` of [lean/OAI/Computability/TypeSystem/Equivalence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Equivalence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`):
--
--   ```lean
--   theorem classPred_typed {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
--       HasType P Γ (B.classPred L.code KY.code KP.code y) B.predType ∧
--         WellModed γ (B.classPred L.code KY.code KP.code y) .data
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.HasType`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.QuantifierRoute`, `OAI.PureTypeSystem.Labelled.SpecializedCode`, `OAI.PureTypeSystem.Labelled.WellModed`, `OAI.PureTypeSystem.Labelled.LogicSetup.code`, `OAI.PureTypeSystem.Labelled.QuantifierRoute.code`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed`, `OAI.PureTypeSystem.Labelled.SpecializedCode.classPred`, `OAI.PureTypeSystem.Labelled.SpecializedCode.predType` and `OAI.PureTypeSystem.Labelled.SpecializedCode.yType` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proofs of `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.class_witness_intro` and `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.edge_classes_witness_elim` of this split import it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Equivalence.lean (declaration OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.classPred_typed)

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

universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem classPred_typed {y : Expr S} (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    HasType P Γ (B.classPred L.code KY.code KP.code y) B.predType ∧
      WellModed γ (B.classPred L.code KY.code KP.code y) .data := by
  sorry

end

end SpecializedCode.Formed

end PureTypeSystem.Labelled

end OAI
end
