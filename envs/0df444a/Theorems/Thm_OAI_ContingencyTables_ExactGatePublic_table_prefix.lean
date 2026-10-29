-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ExactGatePublic_table_prefix
-- name    : OAI.ContingencyTables.ExactGatePublic.table_prefix
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:51:51.03198+00:00
-- url     : https://prove2.me/theorems/0ad627f3-d8f5-4ce3-928f-c42e0535e88e
-- title:
--   OAI.ContingencyTables.ExactGatePublic.table_prefix: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ExactGatePublic.table_prefix` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePublic.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePublic.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ExactGatePublic`, with `open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing`, `open DensePrograms ProfilePrograms SmallGraphProfiles`, `open ExactTablePrefix (code decode input)`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem table_prefix (htotal : (∑ i,r i)=∑ j,c j) (B : ℕ)
--       (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B) :
--       ∃ p,Implements ExactPhysicalProgram.program.table (output r c)
--         (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (input r c)))) p ∧
--         (∀ g : Option (Table r c) → ℚ,p.mean g=(experiment r c).mean g) ∧
--         p.cost≤ExactGatePhysical.budget (input r c) B
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.Realizer` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.DensePrograms.matrixCode` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.GreedyFeasibleTable.printMatrix`, `OAI.MatchingFPRAS.PhysicalPost.Implements`, `OAI.MatchingFPRAS.PhysicalStream.Experiment`, `OAI.MatchingFPRAS.PhysicalPost.Program`, `OAI.MatchingFPRAS.PhysicalPost.Program.initial`, `OAI.MatchingFPRAS.PhysicalStream.Experiment.cost` and `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.GreedyFeasibleTable.printMatrixRealizer` and `OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol` (definitions bundle `OAIQ089A007` of this split); `OAI.MatchingFPRAS.TreePost.packed` (definitions bundle `OAIQ089A008` of this split); `OAI.ContingencyTables.ExactGatePhysical.budget`, `OAI.ContingencyTables.ExactGatePublic.experiment`, `OAI.ContingencyTables.ExactGatePublic.output`, `OAI.ContingencyTables.ExactPhysicalProgram.program` and `OAI.ContingencyTables.ExactTablePrefix.input` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.HasMargins`, `OAI.ContingencyTables.Table` and `OAI.MatchingFPRAS.Symbol` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.exactSampling` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactGatePublic.lean (declaration OAI.ContingencyTables.ExactGatePublic.table_prefix)

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

namespace ContingencyTables.ExactGatePublic
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms ProfilePrograms SmallGraphProfiles
open ExactTablePrefix (code decode input)
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

attribute [local irreducible] exactOrdinary

theorem table_prefix (htotal : (∑ i,r i)=∑ j,c j) (B : ℕ)
    (hB : ∀ X : Table r c,GreedyFeasibleTable.printMatrixRealizer.cost (matrixCode X.val)≤B) :
    ∃ p,Implements ExactPhysicalProgram.program.table (output r c)
      (ExactPhysicalProgram.program.initial (Tape.mk₁ (TreePost.packed (input r c)))) p ∧
      (∀ g : Option (Table r c) → ℚ,p.mean g=(experiment r c).mean g) ∧
      p.cost≤ExactGatePhysical.budget (input r c) B := by
  sorry

end
end ContingencyTables.ExactGatePublic

end OAI
end
