-- Prove2me | Theorems.Thm_OAI_ContingencyTables_ExactPublicLaw_halted_feasible
-- name    : OAI.ContingencyTables.ExactPublicLaw.halted_feasible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:52:32.58904+00:00
-- url     : https://prove2.me/theorems/ff883259-e6dc-47f6-a162-d47055638597
-- title:
--   OAI.ContingencyTables.ExactPublicLaw.halted_feasible: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.ExactPublicLaw.halted_feasible` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactPublicLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactPublicLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.ExactPublicLaw`, with `open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing`, `open PhysicalEventBounds PhysicalPublicLaw ExactPublicPrefix SmallGraphProfiles`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem halted_feasible (t : ℕ) (bits : Bits t)
--       (hh : (MatchingFPRAS.run machine (Algorithms.encodeMargins r c) bits).state=none) :
--       ∃ X : Table r c,Algorithms.OutputsTable machine (Algorithms.encodeMargins r c) bits X.val
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.GridBoundary.Grid` (definitions bundle `OAIQ089A001` of this split); `OAI.MatchingFPRAS.PhysicalStream.Bits` (definitions bundle `OAIQ089A002` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.ExactPublicPrefix.machine` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.HasMargins`, `OAI.ContingencyTables.Table`, `OAI.MatchingFPRAS.run`, `OAI.ContingencyTables.Algorithms.OutputsTable`, `OAI.ContingencyTables.Algorithms.encodeMargins`, `OAI.MatchingFPRAS.Configuration` and `OAI.MatchingFPRAS.RandomMachine` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.exactSampling` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactPublicLaw.lean (declaration OAI.ContingencyTables.ExactPublicLaw.halted_feasible)

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

namespace ContingencyTables.ExactPublicLaw
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.PhysicalPost Turing
open PhysicalEventBounds PhysicalPublicLaw ExactPublicPrefix SmallGraphProfiles
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] ExactPublicPrefix.program ExactPublicPrefix.output
  ExactTablePrefix.experiment correctionPrecision
  PublishedInputs.FiniteBoxPrekopaLeindler PublishedInputs.FiniteCheeger
  CompletionCounts.dimensionAllowance

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

section Conditional
variable
    (hPL : ∀ q,PublishedInputs.FiniteBoxPrekopaLeindler q)
    (hCheeger : ∀ q k,PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin q) (4*k^8)))
    (htotal : (∑ i,r i)=∑ j,c j)
include hPL hCheeger htotal

theorem halted_feasible (t : ℕ) (bits : Bits t)
    (hh : (MatchingFPRAS.run machine (Algorithms.encodeMargins r c) bits).state=none) :
    ∃ X : Table r c,Algorithms.OutputsTable machine (Algorithms.encodeMargins r c) bits X.val := by
  sorry

end Conditional
end
end ContingencyTables.ExactPublicLaw

end OAI
end
