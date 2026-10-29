-- Prove2me | Theorems.Thm_OAI_ContingencyTables_SmallGraphProfiles_allSamplingMachineTime_public_bound
-- name    : OAI.ContingencyTables.SmallGraphProfiles.allSamplingMachineTime_public_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:05:51.53199+00:00
-- url     : https://prove2.me/theorems/287626be-7bbc-4d8b-9250-41380e7ecb61
-- title:
--   OAI.ContingencyTables.SmallGraphProfiles.allSamplingMachineTime_public_bound: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.SmallGraphProfiles.allSamplingMachineTime_public_bound` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/AllSamplingMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/AllSamplingMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.SmallGraphProfiles`, with `open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal`, `open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.TreeTyped Turing Algorithms Polynomial`, `open ResidualMixture FirstSuccess FairBits`, `open scoped BigOperators Classical`):
--
--   ```lean
--   lemma allSamplingMachineTime_public_bound :
--       ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
--         (∑ i,r i)=∑ j,c j → ∀ k,
--         allSamplingMachineTime (encodeSamplingInput r c k)≤C*(samplingSize n r k)^d
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.ProfilePrograms.allSamplingMachineTime` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.Algorithms.encodeSamplingInput` and `OAI.ContingencyTables.Algorithms.samplingSize` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.boundedSampling` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/AllSamplingMachine.lean (declaration OAI.ContingencyTables.SmallGraphProfiles.allSamplingMachineTime_public_bound)

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

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open MatchingFPRAS MatchingFPRAS.PhysicalStream MatchingFPRAS.TreeTyped Turing Algorithms Polynomial
open ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section

lemma allSamplingMachineTime_public_bound :
    ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → ∀ k,
      allSamplingMachineTime (encodeSamplingInput r c k)≤C*(samplingSize n r k)^d := by
  sorry

end
end ContingencyTables.SmallGraphProfiles

end OAI
end
