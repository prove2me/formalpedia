-- Prove2me | Theorems.Thm_OAI_WitnessedSeparation_Grid_QuotedGrid_formula_value
-- name    : OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T00:22:53.39179+00:00
-- url     : https://prove2.me/theorems/a93468ba-4ac7-44d3-8342-507026738b0b
-- title:
--   OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value: intermediate lemma from OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WitnessedChoice.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting*, OpenAI Math Release, September 24, 2026, result family 243, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value` of [lean/OAI/Computability/WitnessedChoice/ChoiceSeparation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WitnessedChoice/ChoiceSeparation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WitnessedSeparation.Grid.QuotedGrid`, with `open Classical WitnessedChoice WitnessedChoice.BGS Hereditary`, `open SourceProgram`):
--
--   ```lean
--   lemma formula_value (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) :
--       program.formula.eval (atomInput b) p Fin.elim0 = some (decide (∑ v, b v = 0))
--   ```
--
--   **Definitions.** The statement is written with `OAI.WitnessedSeparation.Grid.Atom`, `OAI.WitnessedSeparation.Grid.GridResources`, `OAI.WitnessedSeparation.Grid.Scalar`, `OAI.WitnessedSeparation.Grid.Vertex`, `OAI.WitnessedSeparation.Grid.atomInput`, `OAI.WitnessedSeparation.Grid.instFintypeAtom`, `OAI.WitnessedChoice.BGS.ClosedGuardedProgram.formula` and `OAI.WitnessedChoice.BGS.SourceProgram.program` (definitions bundle `OAIQ4Wc000` of this split); `OAI.WitnessedChoice.BGS.Result` and `OAI.WitnessedSeparation.Hereditary.HF` (the published bundle `Def_WitnessedChoice`).
--
--   **Used by.** The proof of `OAI.WitnessedChoice.main` of this split imports it.
-- source:
--   OpenAI, Witnessed symmetric choice is strictly stronger than choiceless polynomial time with counting, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 243; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Witnessed-symmetric-choice-is-strictly-stronger-than-choiceless-polynomial-time-with-counting-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/WitnessedChoice/ChoiceSeparation.lean (declaration OAI.WitnessedSeparation.Grid.QuotedGrid.formula_value)

import Mathlib
import Definitions.Def_WitnessedChoice
import Definitions.Def_OAIQ4Wc000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WitnessedSeparation.Grid

noncomputable section

open Classical WitnessedChoice WitnessedChoice.BGS Hereditary

variable {n : ℕ} {b : Vertex n → Scalar}

namespace QuotedGrid

open SourceProgram

attribute [local irreducible] SourceProgram.parameters SourceProgram.candidates
  SourceProgram.cycles SourceProgram.output

lemma formula_value (p : Polynomial ℝ) (hp : GridResources p b) (hn : 1 ≤ n) :
    program.formula.eval (atomInput b) p Fin.elim0 = some (decide (∑ v, b v = 0)) := by
  sorry

end QuotedGrid

end

end WitnessedSeparation.Grid

end OAI
end
