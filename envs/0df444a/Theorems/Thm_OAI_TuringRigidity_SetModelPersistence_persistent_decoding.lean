-- Prove2me | Theorems.Thm_OAI_TuringRigidity_SetModelPersistence_persistent_decoding
-- name    : OAI.TuringRigidity.SetModelPersistence.persistent_decoding
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:48.429234+00:00
-- url     : https://prove2.me/theorems/e8674bbf-539d-4916-882d-62a0072d6c45
-- title:
--   OAI.TuringRigidity.SetModelPersistence.persistent_decoding: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.SetModelPersistence.persistent_decoding` of [lean/OAI/Computability/DegreeRigidity/SetModels/SetModelPersistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/SetModelPersistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.SetModelPersistence`, with `open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals`, `open SetDegreeDecoding SetModelSequences SetModelColumns EncodedForcing`, `open PersistentRestrictions PersistentPresentation PersistentCountability`):
--
--   ```lean
--   theorem persistent_decoding (M : ZFSet.{u}) (hM : Transitive M)
--       (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
--       (hS : Separation M) (hI : Infinity M)
--       (hC : PersistenceRealClosure.Closed (reals M))
--       {p E : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hEM : E ∈ M)
--       (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
--         ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
--       {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
--       (ρ : I ≃o I) (hρ : Persistent I ρ)
--       (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
--       idealSet I ∈ M ∧ automorphismSet ρ ∈ M
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.SetDegreeDecoding.idealSet`, `OAI.TuringRigidity.SetModelReals.realSet`, `OAI.TuringRigidity.SetModelReals.reals` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.Infinity`, `OAI.TuringRigidity.BoundedSetTheory.Pairing`, `OAI.TuringRigidity.BoundedSetTheory.PowerSet` and `OAI.TuringRigidity.BoundedSetTheory.Union` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.Separation` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistenceRealClosure.Closed`, `OAI.TuringRigidity.PersistentPresentation.Presented`, `OAI.TuringRigidity.PersistentRestrictions.Persistent` and `OAI.TuringRigidity.SetModelSequences.PairingCode` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute`, `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute`, `OAI.TuringRigidity.BoundedSetTheory.InternalCollapse.real_collapse_reconstructs` and `OAI.TuringRigidity.SetModelCountability.persistent_countable_extensions` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/SetModelPersistence.lean (declaration OAI.TuringRigidity.SetModelPersistence.persistent_decoding)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003
import Definitions.Def_OAIQ064A004

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelPersistence
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals
open SetDegreeDecoding SetModelSequences SetModelColumns EncodedForcing
open PersistentRestrictions PersistentPresentation PersistentCountability
universe u
noncomputable section

theorem persistent_decoding (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hC : PersistenceRealClosure.Closed (reals M))
    {p E : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hEM : E ∈ M)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    idealSet I ∈ M ∧ automorphismSet ρ ∈ M := by
  sorry

end
end TuringRigidity.SetModelPersistence

end OAI
end
