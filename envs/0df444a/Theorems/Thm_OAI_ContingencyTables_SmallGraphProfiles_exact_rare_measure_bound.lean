-- Prove2me | Theorems.Thm_OAI_ContingencyTables_SmallGraphProfiles_exact_rare_measure_bound
-- name    : OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:13:54.817859+00:00
-- url     : https://prove2.me/theorems/45819083-20fd-4043-b59b-6a5041dc9cd3
-- title:
--   OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound` of [lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactRareMeasureBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactRareMeasureBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.SmallGraphProfiles`, with `open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem exact_rare_measure_bound : ∃ p a : Polynomial ℕ,
--       ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
--       exactRareMeasure (List.ofFn r,List.ofFn c) ≤
--         p.eval (a.eval (Algorithms.samplingSize n r 0)*exactBoxScale r c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.ProfilePrograms.exactRareMeasure` (definitions bundle `OAIQ089A009` of this split); `OAI.ContingencyTables.SmallGraphProfiles.exactBoxScale` (definitions bundle `OAIQ089A011` of this split); `OAI.ContingencyTables.Algorithms.samplingSize` (the published bundle `Def_ContingencyTables`).
--
--   **Used by.** The proof of `OAI.ContingencyTables.SmallGraphProfiles.exact_public_correction_bound` of this split imports it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Sampling/ExactRareMeasureBound.lean (declaration OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial
open scoped BigOperators Classical
noncomputable section

theorem exact_rare_measure_bound : ∃ p a : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    exactRareMeasure (List.ofFn r,List.ofFn c) ≤
      p.eval (a.eval (Algorithms.samplingSize n r 0)*exactBoxScale r c) := by
  sorry

end
end ContingencyTables.SmallGraphProfiles

end OAI
end
