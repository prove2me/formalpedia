-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ExactPublicPrefix_prefix_correct
-- name    : OAI.ContingencyTables.ExactPublicPrefix.prefix_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:52:57.675007+00:00
-- url     : https://prove2.me/theorems/315758c7-56bf-43b9-9880-59347690ca23
-- title:
--   OAI.ContingencyTables.ExactPublicPrefix.prefix_correct: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ExactPublicPrefix.prefix_correct` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactPublicPrefix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactPublicPrefix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ExactPublicPrefix`, with `open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing`, `open DensePrograms`, `open scoped Classical`):
--
--   ```lean
--   theorem prefix_correct (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
--       ∃ p,Implements program.table (output r c)
--         (program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) p ∧
--         ∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.PhysicalPost.Implements`, `OAI.MatchingFPRAS.PhysicalStream.Experiment`, `OAI.MatchingFPRAS.PhysicalPost.Program`, `OAI.MatchingFPRAS.PhysicalPost.Program.initial` and `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.ExactPublicPrefix.output`, `OAI.ContingencyTables.ExactPublicPrefix.program`, `OAI.ContingencyTables.ExactTablePrefix.experiment` and `OAI.ContingencyTables.ExactTablePrefix.input` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.Table` and `OAI.MatchingFPRAS.Symbol` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proofs of `OAI.ContingencyTables.ExactPublicLaw.haltMass_limit`, `OAI.ContingencyTables.ExactPublicLaw.halted_feasible` and `OAI.ContingencyTables.ExactPublicLaw.tableMass_limit` of this split import it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactPublicPrefix.lean (declaration OAI.ContingencyTables.ExactPublicPrefix.prefix_correct)

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

namespace ContingencyTables.ExactPublicPrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open DensePrograms
open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

theorem prefix_correct (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    ∃ p,Implements program.table (output r c)
      (program.initial (Tape.mk₁ (ExactTablePrefix.input r c))) p ∧
      ∀ g : Option (Table r c) → ℚ,p.mean g=(ExactTablePrefix.experiment r c N).mean g := by
  sorry

end
end ContingencyTables.ExactPublicPrefix

end OAI
end
