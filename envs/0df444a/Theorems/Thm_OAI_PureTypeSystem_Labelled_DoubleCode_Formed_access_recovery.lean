-- Prove2me | Theorems.Thm_OAI_PureTypeSystem_Labelled_DoubleCode_Formed_access_recovery
-- name    : OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:56:16.328432+00:00
-- url     : https://prove2.me/theorems/90c41b65-e4c4-49cd-984b-0ead7a066764
-- title:
--   OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery: intermediate lemma from OpenAI, Weak and strong normalization in pure type systems
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PureTypeSystem.weak_implies_strong`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak and strong normalization in pure type systems*, OpenAI Math Release, September 25, 2026, result family 245, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery` of [lean/OAI/Computability/TypeSystem/Pairs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Pairs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PureTypeSystem.Labelled.DoubleCode.Formed`):
--
--   ```lean
--    theorem access_recovery {T pMap m c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
--       (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap)
--       (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data)
--       (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
--       (hc : HasType P Γ c T) (mc : WellModed γ c .data)
--       {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
--       (hnd : Proves P Γ γ (L.neg (R.isDummy L.code T m))) :
--       Equivalent P Γ γ
--         (R.recoverAccess U L.code T
--           (R.bundle L.code (R.paramType T) (R.dummy L.code T) m (R.point U L.code T c₀ c)) pMap)
--         (U.observe T (pMap.instantiate m) c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PureTypeSystem.Labelled.DataMap`, `OAI.PureTypeSystem.Labelled.DataWrapper`, `OAI.PureTypeSystem.Labelled.DoubleCode`, `OAI.PureTypeSystem.Labelled.Equivalent`, `OAI.PureTypeSystem.Labelled.Expr`, `OAI.PureTypeSystem.Labelled.HasType`, `OAI.PureTypeSystem.Labelled.LogicSetup`, `OAI.PureTypeSystem.Labelled.Mode`, `OAI.PureTypeSystem.Labelled.Proves`, `OAI.PureTypeSystem.Labelled.SortedAt`, `OAI.PureTypeSystem.Labelled.WellModed`, `OAI.PureTypeSystem.Labelled.DataWrapper.Formed`, `OAI.PureTypeSystem.Labelled.DataWrapper.apply`, `OAI.PureTypeSystem.Labelled.DoubleCode.Formed`, `OAI.PureTypeSystem.Labelled.DoubleCode.bpType`, `OAI.PureTypeSystem.Labelled.DoubleCode.bundle`, `OAI.PureTypeSystem.Labelled.DoubleCode.dummy`, `OAI.PureTypeSystem.Labelled.DoubleCode.isDummy`, `OAI.PureTypeSystem.Labelled.DoubleCode.paramType`, `OAI.PureTypeSystem.Labelled.DoubleCode.point`, `OAI.PureTypeSystem.Labelled.DoubleCode.recoverAccess`, `OAI.PureTypeSystem.Labelled.Expr.instantiate`, `OAI.PureTypeSystem.Labelled.LogicSetup.code` and `OAI.PureTypeSystem.Labelled.LogicSetup.neg` (definitions bundle `OAIQ5T6000` of this split); `OAI.PureTypeSystem.Specification` (the published bundle `Def_TypeSystemNormalization`).
--
--   **Used by.** The proofs of `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.delta_valid`, `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_lift_validStep`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.probe_exact`, `OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.responseProbe_compare` and `OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_shift_compare_at` of this split import it.
-- source:
--   OpenAI, Weak and strong normalization in pure type systems, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 245; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-and-strong-normalization-in-pure-type-systems-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/TypeSystem/Pairs.lean (declaration OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery)

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
namespace DoubleCode

section
variable (R : DoubleCode S)
namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H) (hI : I.Nonempty) (hH : H.Nonempty)
include h hU hI hH

 theorem access_recovery {T pMap m c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap)
    (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hnd : Proves P Γ γ (L.neg (R.isDummy L.code T m))) :
    Equivalent P Γ γ
      (R.recoverAccess U L.code T
        (R.bundle L.code (R.paramType T) (R.dummy L.code T) m (R.point U L.code T c₀ c)) pMap)
      (U.observe T (pMap.instantiate m) c) := by
  sorry
end Formed
end

end DoubleCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end
