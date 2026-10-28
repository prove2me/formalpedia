-- Prove2me | Theorems.Thm_OAI_TuringRigidity_SetModelCountability_persistent_countable_extensions
-- name    : OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:47:42.941092+00:00
-- url     : https://prove2.me/theorems/cae774a2-feaa-4f56-8779-0e8346e3e4ca
-- title:
--   OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions` of [lean/OAI/Computability/DegreeRigidity/SetModels/SetModelCountableExtensions.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/SetModelCountableExtensions.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.SetModelCountability`, with `open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax`, `open SetDegreeDecoding PersistentRestrictions PersistentPresentation EncodedForcing`):
--
--   ```lean
--   theorem persistent_countable_extensions (C : Context M) (hCh : InternalChoice M)
--       (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
--       (ρ : I ≃o I) (hρ : Persistent I ρ)
--       (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
--       {X : Oracle} (hX : X ∈ reals M) :
--       ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
--         degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
--         idealSet J ∈ M ∧ automorphismSet σ ∈ M ∧ InternallyCountable M (idealSet J)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.SetDegreeDecoding.idealSet`, `OAI.TuringRigidity.SetModelCountability.InternallyCountable` and `OAI.TuringRigidity.SetModelReals.reals` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.Extends`, `OAI.TuringRigidity.PersistentRestrictions.Persistent` and `OAI.TuringRigidity.SetModelCountability.InternalChoice` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.SetModelFunctions.Context` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/SetModelCountableExtensions.lean (declaration OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A007

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem persistent_countable_extensions (C : Context M) (hCh : InternalChoice M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M ∧ InternallyCountable M (idealSet J) := by
  sorry

end
end TuringRigidity.SetModelCountability

end OAI
end
