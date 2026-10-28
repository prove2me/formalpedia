-- Prove2me | Theorems.Thm_OAI_TuringRigidity_PersistentRestrictionCode_restriction
-- name    : OAI.TuringRigidity.PersistentRestrictionCode.restriction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:50:26.984738+00:00
-- url     : https://prove2.me/theorems/2f1a82aa-b973-4f02-adae-96990dfa60ff
-- title:
--   OAI.TuringRigidity.PersistentRestrictionCode.restriction: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.PersistentRestrictionCode.restriction` of [lean/OAI/Computability/DegreeRigidity/Constructibility/PersistentRestrictionCode.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/PersistentRestrictionCode.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.PersistentRestrictionCode`, with `open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation IdealLocality`, `open PersistentRestrictions PersistentLocality PersistentPresentation`):
--
--   ```lean
--   theorem restriction {I J K : CountableIdeal} (ρ : I ≃o I) (τ : K ≃o K)
--       (hIK : I.carrier ⊆ K.carrier) (he : Extends hIK ρ τ)
--       (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
--       (hIJ : I.carrier ⊆ J.carrier) (hJK : J.carrier ⊆ K.carrier)
--       (hj : JumpClosed (ideal J)) {H : Oracle} (hpres : Presented J H)
--       (hLK : (JumpIdeal.generated (degree H)).carrier ⊆ K.carrier) :
--       ∃ σ : J ≃o J, Extends hIJ ρ σ ∧ Extends hJK σ τ ∧
--         RecursivePred (iterate H 11) (Graph σ hpres)
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.ArithmeticHierarchy.RecursivePred`, `OAI.TuringRigidity.OracleJump.iterate`, `OAI.TuringRigidity.OracleJump.jump` and `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentPresentation.Graph`, `OAI.TuringRigidity.PersistentPresentation.Presented` and `OAI.TuringRigidity.PersistentRestrictions.Extends` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.IdealLocality.JumpClosed` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.JumpIdeal.generated` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.PersistentLocality.ideal` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.ArithmeticPersistence.persistent_iff`, `OAI.TuringRigidity.ArithmeticTree.native_internal_matrix` and `OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Constructibility/PersistentRestrictionCode.lean (declaration OAI.TuringRigidity.PersistentRestrictionCode.restriction)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentRestrictionCode
open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation IdealLocality
open PersistentRestrictions PersistentLocality PersistentPresentation
noncomputable section

theorem restriction {I J K : CountableIdeal} (ρ : I ≃o I) (τ : K ≃o K)
    (hIK : I.carrier ⊆ K.carrier) (he : Extends hIK ρ τ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hJK : J.carrier ⊆ K.carrier)
    (hj : JumpClosed (ideal J)) {H : Oracle} (hpres : Presented J H)
    (hLK : (JumpIdeal.generated (degree H)).carrier ⊆ K.carrier) :
    ∃ σ : J ≃o J, Extends hIJ ρ σ ∧ Extends hJK σ τ ∧
      RecursivePred (iterate H 11) (Graph σ hpres) := by
  sorry

end
end TuringRigidity.PersistentRestrictionCode

end OAI
end
