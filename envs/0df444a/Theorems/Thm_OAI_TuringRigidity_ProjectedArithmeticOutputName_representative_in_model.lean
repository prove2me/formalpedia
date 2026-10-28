-- Prove2me | Theorems.Thm_OAI_TuringRigidity_ProjectedArithmeticOutputName_representative_in_model
-- name    : OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:42:34.397+00:00
-- url     : https://prove2.me/theorems/9e4c2e10-da41-4f80-b7bf-49730416694b
-- title:
--   OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model` of [lean/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputName.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputName.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.ProjectedArithmeticOutputName`, with `open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing`, `open CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric`, `open PersistentRestrictions OracleJump`):
--
--   ```lean
--   theorem representative_in_model (N : ZFSet.{0}) (hN : Transitive N) (hTN : SourceT N)
--       (I J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
--       (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
--       (A R : Oracle) (hA : degree A ∈ J.carrier)
--       (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
--       (hAN : A ∈ modelReals N) (hRN : R ∈ modelReals N) :
--       ∃ X : Oracle, X ∈ modelReals N ∧ degree X = (σ ⟨degree A,hA⟩).val ∧
--         Reduces X (iterate (join A R) 5) ∧ ∃ e : OracleCode,
--           OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.OracleCode`, `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.join`, `OAI.TuringRigidity.OracleCode.eval`, `OAI.TuringRigidity.OracleJump.iterate`, `OAI.TuringRigidity.OracleJump.jump`, `OAI.TuringRigidity.PersistentRestrictions.CountableIdeal` and `OAI.TuringRigidity.TransitiveNameModel.Transitive` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedSetTheory.SourceT` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.PersistentRestrictions.Extends` (definitions bundle `OAIQ064A004` of this split); `OAI.TuringRigidity.BoundedSetTheory.modelReals` (definitions bundle `OAIQ064A006` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle`, `OAI.TuringRigidity.Reduces`, `OAI.TuringRigidity.instPartialOrderDegree` and `OAI.TuringRigidity.oracleFunction` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/ProjectedArithmeticOutputName.lean (declaration OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006

section

attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ProjectedArithmeticOutputName
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open PersistentRestrictions OracleJump
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem representative_in_model (N : ZFSet.{0}) (hN : Transitive N) (hTN : SourceT N)
    (I J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (hAN : A ∈ modelReals N) (hRN : R ∈ modelReals N) :
    ∃ X : Oracle, X ∈ modelReals N ∧ degree X = (σ ⟨degree A,hA⟩).val ∧
      Reduces X (iterate (join A R) 5) ∧ ∃ e : OracleCode,
        OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X := by
  sorry

end TuringRigidity.ProjectedArithmeticOutputName

end OAI
end
