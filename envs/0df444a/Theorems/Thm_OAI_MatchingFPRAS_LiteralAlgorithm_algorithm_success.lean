-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_LiteralAlgorithm_algorithm_success
-- name    : OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:02:23.433176+00:00
-- url     : https://prove2.me/theorems/9b140a95-8573-4288-bb92-ea5676d5671d
-- title:
--   OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/AlgorithmLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/AlgorithmLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.LiteralAlgorithm`, with `open scoped Classical`, `open TreeTyped TreeFraction PhysicalStream LiteralInput`):
--
--   ```lean
--   lemma algorithm_success (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0<δ) :
--       1-δ≤(algorithm (encodeInput G ε δ)).mean (fun as=>if AccurateWord G ε as then 1 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.LiteralAlgorithm.AccurateWord` and `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput`, `OAI.MatchingFPRAS.Symbol` and `OAI.MatchingFPRAS.encodeInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.thm_main` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/AlgorithmLaw.lean (declaration OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open scoped Classical
open TreeTyped TreeFraction PhysicalStream LiteralInput

lemma algorithm_success (G : GraphInput) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0<δ) :
    1-δ≤(algorithm (encodeInput G ε δ)).mean (fun as=>if AccurateWord G ε as then 1 else 0) := by
  sorry
end MatchingFPRAS.LiteralAlgorithm

end OAI
end
