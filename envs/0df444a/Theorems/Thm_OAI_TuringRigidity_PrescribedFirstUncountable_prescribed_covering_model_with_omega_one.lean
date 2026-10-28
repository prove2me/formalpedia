-- Prove2me | Theorems.Thm_OAI_TuringRigidity_PrescribedFirstUncountable_prescribed_covering_model_with_omega_one
-- name    : OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:50:53.805413+00:00
-- url     : https://prove2.me/theorems/6832d260-fa8e-4233-bbc7-2ba1da9e95bc
-- title:
--   OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one` of [lean/OAI/Computability/DegreeRigidity/Representation/PrescribedFirstUncountable.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/PrescribedFirstUncountable.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.PrescribedFirstUncountable`, with `open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible SetDegreeDecoding`, `open PersistentRestrictions ArithmeticTree`):
--
--   ```lean
--   theorem prescribed_covering_model_with_omega_one (π : Degree ≃o Degree) (A : ℕ → Oracle) :
--       ∃ M : ZFSet.{0}, ∃ hM : Transitive M, ∃ hT : SourceT M,
--         ∃ hcount : Countable (Conditions M),
--           letI := hcount
--           Valid M ∧ (∃ K, InternalCountableOrdinals.FirstUncountable M K) ∧ (∀ n, A n ∈ modelReals M) ∧
--           (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
--             π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) ∧
--           ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
--             RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
--             automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
--             SetGenericallyPersistent M _ ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.instSemilatticeSupDegree`, `OAI.TuringRigidity.ArithmeticTree.SetGenericallyPersistent`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.SetDegreeDecoding.automorphismSet`, `OAI.TuringRigidity.TransitiveNameModel.Conditions`, `OAI.TuringRigidity.TransitiveNameModel.Transitive` and `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.InternalCountableOrdinals.FirstUncountable` and `OAI.TuringRigidity.RelativeConstructible.groundReals` (definitions bundle `OAIQ064A001` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.Persistent` and `OAI.TuringRigidity.PersistentRestrictions.RestrictsTo` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals` and `OAI.TuringRigidity.ElementaryModel.Valid` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.RelativeConstructible.relativeModel` (definitions bundle `OAIQ064A007` of this split); `OAI.TuringRigidity.ElementaryModel.modelIdeal` (definitions bundle `OAIQ064A008` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.ManuscriptMain.rigidity` and `OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/PrescribedFirstUncountable.lean (declaration OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

section

attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PrescribedFirstUncountable
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible SetDegreeDecoding
open PersistentRestrictions ArithmeticTree

theorem prescribed_covering_model_with_omega_one (π : Degree ≃o Degree) (A : ℕ → Oracle) :
    ∃ M : ZFSet.{0}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        Valid M ∧ (∃ K, InternalCountableOrdinals.FirstUncountable M K) ∧ (∀ n, A n ∈ modelReals M) ∧
        (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
          π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) ∧
        ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
          RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
          automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
          SetGenericallyPersistent M _ ρ := by
  sorry

end TuringRigidity.PrescribedFirstUncountable

end OAI
end
