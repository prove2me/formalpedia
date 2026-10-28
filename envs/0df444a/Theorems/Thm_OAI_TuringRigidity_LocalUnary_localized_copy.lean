-- Prove2me | Theorems.Thm_OAI_TuringRigidity_LocalUnary_localized_copy
-- name    : OAI.TuringRigidity.LocalUnary.localized_copy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:04.864307+00:00
-- url     : https://prove2.me/theorems/7e43af11-772b-404d-9bc6-ecbe17a10267
-- title:
--   OAI.TuringRigidity.LocalUnary.localized_copy: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.LocalUnary.localized_copy` of [lean/OAI/Computability/DegreeRigidity/Effective/LocalUnary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Effective/LocalUnary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.LocalUnary`, with `open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump`, `open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding`):
--
--   ```lean
--   theorem localized_copy (X : Oracle) : ∃ c : Copy (fun n => X n = true),
--       RelationBelow c.successor (degree (join X (jump FixedArithmetic.zero))) ∧
--         RelationBelow c.predicate (degree (join X (jump FixedArithmetic.zero)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.join`, `OAI.TuringRigidity.ArithmeticModelDecoding.Copy` and `OAI.TuringRigidity.OracleJump.jump` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedDecoding.RelationBelow` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.Oracle` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.ArithmeticPersistence.persistent_iff`, `OAI.TuringRigidity.FullSetForcing.prescribed_one_real_names`, `OAI.TuringRigidity.PersistentRestrictionCode.restriction`, `OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one`, `OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model` and `OAI.TuringRigidity.SetModelPersistence.persistent_decoding` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Effective/LocalUnary.lean (declaration OAI.TuringRigidity.LocalUnary.localized_copy)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A002
import Definitions.Def_OAIQ064A003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalUnary
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding
noncomputable section
attribute [local instance] Classical.propDecidable

theorem localized_copy (X : Oracle) : ∃ c : Copy (fun n => X n = true),
    RelationBelow c.successor (degree (join X (jump FixedArithmetic.zero))) ∧
      RelationBelow c.predicate (degree (join X (jump FixedArithmetic.zero))) := by
  sorry

end
end TuringRigidity.LocalUnary

end OAI
end
