-- Prove2me | Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_global_arithmetic_generic_program
-- name    : OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:46.172802+00:00
-- url     : https://prove2.me/theorems/ef689091-0c3d-436e-a61f-bbd1c59a1f68
-- title:
--   OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program` of [lean/OAI/Computability/DegreeRigidity/Representation/GlobalArithmeticGenericProgram.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/GlobalArithmeticGenericProgram.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.RelativeConstructible`, with `open TransitiveNameModel BoundedSetTheory CountableForcing ElementaryModel PersistentRestrictions`, `open GenericIdentity OracleJump CohenColumnRealName`):
--
--   ```lean
--   theorem global_arithmetic_generic_program (π : Degree ≃o Degree) :
--       ∃ (R : Oracle) (p : OracleCode),
--         degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
--         ∀ Y : Oracle, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) Y →
--           RepresentsAt π p (iterate R 5) Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.OracleCode`, `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.ArithmeticPrefixForcing.Generic`, `OAI.TuringRigidity.OracleJump.iterate` and `OAI.TuringRigidity.OracleJump.jump` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` and `OAI.TuringRigidity.GenericIdentity.RepresentsAt` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.instPartialOrderDegree` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.ManuscriptMain.rigidity` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Representation/GlobalArithmeticGenericProgram.lean (declaration OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing ElementaryModel PersistentRestrictions
open GenericIdentity OracleJump CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem global_arithmetic_generic_program (π : Degree ≃o Degree) :
    ∃ (R : Oracle) (p : OracleCode),
      degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      ∀ Y : Oracle, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) Y →
        RepresentsAt π p (iterate R 5) Y := by
  sorry

end TuringRigidity.RelativeConstructible

end OAI
end
