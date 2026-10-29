-- Prove2me | Theorems.Thm_OAI_ContingencyTables_SmallGraphProfiles_scheduledCounts_actual
-- name    : OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:08:49.558026+00:00
-- url     : https://prove2.me/theorems/9e247ada-40c3-4fdb-8c21-d7622d5bdfb0
-- title:
--   OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual` of [lean/OAI/Combinatorics/ContingencyTables/Machines/ScheduledCountSemantics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Machines/ScheduledCountSemantics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.SmallGraphProfiles`, with `open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal`, `open SmallContextCoordinates CompletionCounts OriginalTableBox ResidualMixture FirstSuccess`, `open scoped BigOperators Classical`):
--
--   ```lean
--   lemma scheduledCounts_actual (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
--       scheduledCounts ((List.ofFn r,List.ofFn c),k)=
--         List.ofFn (((scheduledCountsLaw r c htotal k).push (index r c le_rfl)).count)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.CompletionCounts.dimensionAllowance` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.outerTrials`, `OAI.ContingencyTables.IntegerLaw`, `OAI.ContingencyTables.IntegerLaw.push` and `OAI.ContingencyTables.OriginalTableBox.Index` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.OriginalTableBox.index` (definitions bundle `OAIQ089A008` of this split); `OAI.ContingencyTables.ProfilePrograms.scheduledCounts` and `OAI.ContingencyTables.ProfilePrograms.scheduledTrialDenominator` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.SmallGraphProfiles.scheduledCountsLaw` (definitions bundle `OAIQ089A011` of this split); `OAI.ContingencyTables.Table` and `OAI.ContingencyTables.table_fintype` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proofs of `OAI.ContingencyTables.ExactPublicLaw.tableMass_limit` and `OAI.ContingencyTables.ExactTablePrefix.failure_bound` of this split import it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Machines/ScheduledCountSemantics.lean (declaration OAI.ContingencyTables.SmallGraphProfiles.scheduledCounts_actual)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A011

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates CompletionCounts OriginalTableBox ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] scheduledTrialDenominator scheduledTrialWidth
  scheduledCounts scheduledOuterInput listedOuterCounts unitOuterCounts matrixInput
  scheduledTableDraw listedOuterDraw unitCodeOuterDraw

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

lemma scheduledCounts_actual (htotal : ∑ i,r i=∑ j,c j) (k : ℕ) :
    scheduledCounts ((List.ofFn r,List.ofFn c),k)=
      List.ofFn (((scheduledCountsLaw r c htotal k).push (index r c le_rfl)).count) := by
  sorry

end
end ContingencyTables.SmallGraphProfiles

end OAI
end
