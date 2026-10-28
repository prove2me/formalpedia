-- Prove2me | Theorems.Thm_OAI_TuringRigidity_LocalCoding_selected_antichain
-- name    : OAI.TuringRigidity.LocalCoding.selected_antichain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:30:40.430993+00:00
-- url     : https://prove2.me/theorems/42be6206-b26b-4878-bd81-c04dacde5303
-- title:
--   OAI.TuringRigidity.LocalCoding.selected_antichain: intermediate lemma from OpenAI, Rigidity of the Turing degrees (result family 241)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TuringRigidity.ManuscriptMain.rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rigidity of the Turing degrees (result family 241)*, OpenAI Math Release, September 24, 2026, result family 241, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TuringRigidity.LocalCoding.selected_antichain` of [lean/OAI/Computability/DegreeRigidity/Effective/LocalCoding.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Effective/LocalCoding.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TuringRigidity.LocalCoding`, with `open EncodedForcing StageNormalization AntichainParameters`):
--
--   ```lean
--   theorem selected_antichain {A B X : Oracle} (hAB : Reduces A B) (select : ℕ → ℕ)
--       (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n)))
--       (hAnti : ∀ i j, degree (columns A (select i)) ≤ degree (columns A (select j)) →
--         degree (columns A (select i)) = degree (columns A (select j))) :
--       ∃ g₀ g₁ : Degree, g₀ ⊔ g₁ ≤ degree (join X (OracleJump.jump B)) ∧
--         ∀ x : Degree, CodedAntichain (degree B) g₀ g₁ x ↔ ∃ k, degree (columns A (select k)) = x
--   ```
--
--   **Definitions.** The statement is written with `OAI.TuringRigidity.degree`, `OAI.TuringRigidity.instSemilatticeSupDegree`, `OAI.TuringRigidity.join`, `OAI.TuringRigidity.AntichainParameters.CodedAntichain`, `OAI.TuringRigidity.EncodedForcing.columns` and `OAI.TuringRigidity.OracleJump.jump` (definitions bundle `OAIQ064A000` of this split); `OAI.TuringRigidity.Degree`, `OAI.TuringRigidity.Oracle`, `OAI.TuringRigidity.Reduces`, `OAI.TuringRigidity.instPartialOrderDegree` and `OAI.TuringRigidity.oracleFunction` (the published bundle `Def_DegreeRigidity`).
--
--   **Used by.** The proof of `OAI.TuringRigidity.LocalUnary.localized_copy` of this split imports it.
-- source:
--   OpenAI, Rigidity of the Turing degrees (result family 241), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 241; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rigidity-of-the-Turing-degrees-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/DegreeRigidity/Effective/LocalCoding.lean (declaration OAI.TuringRigidity.LocalCoding.selected_antichain)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalCoding
open EncodedForcing StageNormalization AntichainParameters

theorem selected_antichain {A B X : Oracle} (hAB : Reduces A B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n)))
    (hAnti : ∀ i j, degree (columns A (select i)) ≤ degree (columns A (select j)) →
      degree (columns A (select i)) = degree (columns A (select j))) :
    ∃ g₀ g₁ : Degree, g₀ ⊔ g₁ ≤ degree (join X (OracleJump.jump B)) ∧
      ∀ x : Degree, CodedAntichain (degree B) g₀ g₁ x ↔ ∃ k, degree (columns A (select k)) = x := by
  sorry

end TuringRigidity.LocalCoding

end OAI
end
