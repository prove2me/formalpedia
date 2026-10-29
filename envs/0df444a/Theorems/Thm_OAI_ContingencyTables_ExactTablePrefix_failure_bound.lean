-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ExactTablePrefix_failure_bound
-- name    : OAI.ContingencyTables.ExactTablePrefix.failure_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:07:41.26649+00:00
-- url     : https://prove2.me/theorems/a308ade9-b1a5-4cc6-b015-02b5e159e875
-- title:
--   OAI.ContingencyTables.ExactTablePrefix.failure_bound: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ExactTablePrefix.failure_bound` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactTablePrefix.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactTablePrefix.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ExactTablePrefix`, with `open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost`, `open DensePrograms SmallGraphProfiles Turing`, `open scoped Classical BigOperators`):
--
--   ```lean
--   lemma failure_bound
--       (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
--         (largeTailCount r (d^20)*largeTailCount c (d^20)))
--       (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid
--         (I := Fin (largeTailCount r (d^20)*largeTailCount c (d^20))) (4*d^8)))
--       (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
--       (experiment r c N).mean (fun o => if o=none then 1 else 0)≤
--         (1/(2:ℚ)^(correctionPrecision r c))*(1/2:ℚ)^N
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.CompletionCounts.dimensionAllowance` and `OAI.ContingencyTables.GridBoundary.Grid` (definitions bundle `OAIQ089A001` of this split); `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.SmallGraphProfiles.correctionPrecision` and `OAI.ContingencyTables.SmallGraphProfiles.largeTailCount` (definitions bundle `OAIQ089A007` of this split); `OAI.ContingencyTables.ExactTablePrefix.experiment` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.Table` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proofs of `OAI.ContingencyTables.ExactPublicLaw.haltMass_limit`, `OAI.ContingencyTables.ExactPublicLaw.halted_feasible`, `OAI.ContingencyTables.ExactPublicLaw.tableMass_limit` and `OAI.ContingencyTables.exactSampling` of this split import it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactTablePrefix.lean (declaration OAI.ContingencyTables.ExactTablePrefix.failure_bound)

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

namespace ContingencyTables.ExactTablePrefix
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost
open DensePrograms SmallGraphProfiles Turing
open scoped Classical BigOperators
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)
attribute [local irreducible] ExactCoreProgram.prefixExperiment
  ExactPhysicalProgram.program ExactPhysicalProgram.output

lemma failure_bound
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler
      (largeTailCount r (d^20)*largeTailCount c (d^20)))
    (hCheeger : PublishedInputs.FiniteCheeger (GridBoundary.Grid
      (I := Fin (largeTailCount r (d^20)*largeTailCount c (d^20))) (4*d^8)))
    (htotal : (∑ i,r i)=∑ j,c j) (N : ℕ) :
    (experiment r c N).mean (fun o => if o=none then 1 else 0)≤
      (1/(2:ℚ)^(correctionPrecision r c))*(1/2:ℚ)^N := by
  sorry

end
end ContingencyTables.ExactTablePrefix

end OAI
end
