-- Prove2me | Theorems.Thm_OAI_BinaryMatching_Algorithm_R_partition_bracket
-- name    : OAI.BinaryMatching.Algorithm.R_partition_bracket
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:01:49.909071+00:00
-- url     : https://prove2.me/theorems/1cef64ca-aff3-419b-bfdf-53b123b27a73
-- title:
--   OAI.BinaryMatching.Algorithm.R_partition_bracket: intermediate lemma from OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LoopMatching.fullEndpoint`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint)*, OpenAI Math Release, October 2026, result family not identified here; see lean/formalization.yaml, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinaryMatching.Algorithm.R_partition_bracket` of [lean/OAI/Combinatorics/PerfectMatching/AlgorithmPartition.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/AlgorithmPartition.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinaryMatching.Algorithm`, with `open Finset MatchingEntropy`):
--
--   ```lean
--   theorem R_partition_bracket (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
--       (R G:ℝ)-4*(G.n:ℝ)≤ logZ G ∧ logZ G≤(R G:ℝ)+3*(G.n:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinaryMatching.Algorithm.R` and `OAI.BinaryMatching.Algorithm.logZ` (definitions bundle `OAIW2LM000` of this split); `OAI.BinaryMatching.Input` (the published bundle `Def_SingletonLoopMatching`).
--
--   **Used by.** The proof of `OAI.LoopMatching.fullEndpoint` of this split imports it.
-- source:
--   OpenAI, the Lean development OAI.Computability.LoopMatching (comparator challenge of OAI.LoopMatching.fullEndpoint), OpenAI Math Release, October 2026, https://github.com/openai/math (result family not identified here; see lean/formalization.yaml; paper: https://github.com/openai/math; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/PerfectMatching/AlgorithmPartition.lean (declaration OAI.BinaryMatching.Algorithm.R_partition_bracket)

import Mathlib
import Definitions.Def_SingletonLoopMatching
import Definitions.Def_OAIW2LM000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

theorem R_partition_bracket (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    (R G:ℝ)-4*(G.n:ℝ)≤ logZ G ∧ logZ G≤(R G:ℝ)+3*(G.n:ℝ) := by
  sorry

end
end BinaryMatching.Algorithm
end

end OAI
end
