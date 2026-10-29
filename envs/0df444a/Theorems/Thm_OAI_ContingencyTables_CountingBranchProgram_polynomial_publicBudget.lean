-- Prove2me | Theorems.Thm_OAI_ContingencyTables_CountingBranchProgram_polynomial_publicBudget
-- name    : OAI.ContingencyTables.CountingBranchProgram.polynomial_publicBudget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T03:24:50.424997+00:00
-- url     : https://prove2.me/theorems/4e0dd1ba-b227-4053-a7d0-1a814e7785d5
-- title:
--   OAI.ContingencyTables.CountingBranchProgram.polynomial_publicBudget: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.CountingBranchProgram.polynomial_publicBudget` of [lean/OAI/Combinatorics/ContingencyTables/Counting/CountingBranchProgram.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingBranchProgram.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.CountingBranchProgram`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped`):
--
--   ```lean
--   lemma polynomial_publicBudget (hN : PolynomialTime N) : PolynomialTime (publicBudgetRealizer positive N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeTyped.Realizer`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.NetworkVertexCode.Input`, `OAI.ContingencyTables.ResidualGraphProgram.NatMatrix` and `OAI.MatchingFPRAS.TreeFraction.Fraction` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.CountingBaseProgram.Input` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.CountingBranchProgram.Request` and `OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol` (definitions bundle `OAIQ089A007` of this split); `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ089A008` of this split); `OAI.ContingencyTables.CountingBranchProgram.publicBudget` and `OAI.ContingencyTables.CountingBranchProgram.publicBudgetRealizer` (definitions bundle `OAIQ089A009` of this split); `OAI.MatchingFPRAS.Symbol` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.CountingExecutedMachine.public_time` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Counting/CountingBranchProgram.lean (declaration OAI.ContingencyTables.CountingBranchProgram.polynomial_publicBudget)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

attribute [local irreducible] feasible direct

section Budget
variable (positive : Request → ℕ) (N : Realizer positive)

attribute [local irreducible] feasibleBudget

attribute [local irreducible] budget

lemma polynomial_publicBudget (hN : PolynomialTime N) : PolynomialTime (publicBudgetRealizer positive N) := by
  sorry
end Budget

end ContingencyTables.CountingBranchProgram

end OAI
end
