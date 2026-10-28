-- Prove2me | Theorems.Thm_OAI_TuringRigidity_EnumerationConstruction_enumeration_exists
-- name    : OAI.TuringRigidity.EnumerationConstruction.enumeration_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:36:53.333484+00:00
-- url     : https://prove2.me/theorems/3b94fdd4-6e22-45f7-9ed1-b67b08fa65f4
-- title:
--   OAI.TuringRigidity.EnumerationConstruction.enumeration_exists: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.EnumerationConstruction.enumeration_exists` of [lean/OAI/Computability/DegreeRigidity/SetModels/EnumerationConstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/EnumerationConstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.EnumerationConstruction`, with `open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump`, `open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding EnumerationDecoding`):
--
--   ```lean
--   theorem enumeration_exists (H : Oracle) (hz : Reduces (jump FixedArithmetic.zero) H) :
--       ∃ c : Enumeration, c.output = (fun k => degree (columns H k)) ∧
--         RelationBelow c.successor (degree (jump H)) ∧ RelationBelow c.payload (degree (jump H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.EncodedForcing.columns` and `OAI.TuringRigidity.OracleJump.jump` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.BoundedDecoding.RelationBelow` (definitions bundle `OAIQ064A002` of this split); `OAI.TuringRigidity.EnumerationDecoding.Enumeration` and `OAI.TuringRigidity.FixedArithmetic.zero` (definitions bundle `OAIQ064A003` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle` and `OAI.TuringRigidity.Reduces` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proofs of `OAI.TuringRigidity.ArithmeticPersistence.persistent_iff`, `OAI.TuringRigidity.PersistentRestrictionCode.restriction` and `OAI.TuringRigidity.SetModelPersistence.persistent_decoding` of this split import it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/SetModels/EnumerationConstruction.lean (declaration OAI.TuringRigidity.EnumerationConstruction.enumeration_exists)

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

namespace TuringRigidity.EnumerationConstruction
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding EnumerationDecoding

theorem enumeration_exists (H : Oracle) (hz : Reduces (jump FixedArithmetic.zero) H) :
    ∃ c : Enumeration, c.output = (fun k => degree (columns H k)) ∧
      RelationBelow c.successor (degree (jump H)) ∧ RelationBelow c.payload (degree (jump H)) := by
  sorry

end TuringRigidity.EnumerationConstruction

end OAI
end
