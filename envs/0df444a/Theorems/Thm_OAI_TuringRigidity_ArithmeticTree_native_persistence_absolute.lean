-- Prove2me | Theorems.Thm_OAI_TuringRigidity_ArithmeticTree_native_persistence_absolute
-- name    : OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:34:24.398112+00:00
-- url     : https://prove2.me/theorems/abd05b0f-be5b-4c1a-9792-71cb155f6ae0
-- title:
--   OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute` of [lean/OAI/Computability/DegreeRigidity/Representation/SourceTNativeComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/SourceTNativeComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.ArithmeticTree`, with `open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel`, `open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability`, `open SetModelSatisfaction PersistentRestrictions PersistentPresentation PersistentCountability`):
--
--   ```lean
--   theorem native_persistence_absolute (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
--       {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
--       (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
--       (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
--         ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
--       (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : _root_.OAI.TuringRigidity.SetModelCountability.InternallyCountable M (idealSet I))
--       (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
--       (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
--       persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
--         (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔ Persistent I ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.BoundedSetTheory.cons`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.SetDegreeDecoding.degreeSet`, `OAI.TuringRigidity.SetDegreeDecoding.idealSet`, `OAI.TuringRigidity.SetModelCountability.InternallyCountable`, `OAI.TuringRigidity.SetModelReals.reals`, `OAI.TuringRigidity.SetModelSatisfaction.persistenceFormula`, `OAI.TuringRigidity.TransitiveNameModel.Transitive` and `OAI.TuringRigidity.SetModelSatisfaction.InternalFormula.Realize` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.Persistent` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle`, `OAI.TuringRigidity.Reduces` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.ArithmeticTree.native_nonidentity_absolute` and `OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/SourceTNativeComparison.lean (declaration OAI.TuringRigidity.ArithmeticTree.native_persistence_absolute)

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

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions PersistentPresentation PersistentCountability
universe u
noncomputable section

theorem native_persistence_absolute (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : _root_.OAI.TuringRigidity.SetModelCountability.InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔ Persistent I ρ := by
  sorry

end
end TuringRigidity.ArithmeticTree

end OAI
end
