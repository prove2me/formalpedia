-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_LiteralAlgorithm_algorithm_bound
-- name    : OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:02:46.106853+00:00
-- url     : https://prove2.me/theorems/9f8c6a70-e79e-4f95-93c1-aa914825fb33
-- title:
--   OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OriginalCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OriginalCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.LiteralAlgorithm`, with `open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial`):
--
--   ```lean
--   lemma algorithm_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) (ε δ : ℚ)
--       (_he : 0<ε) (_he1 : ε<1) (_hd : 0≤δ) (x : ℕ),1≤x→
--       (encodeInput G ε δ).length≤x→⌈ε⁻¹⌉₊≤x→Nat.clog 2 ⌈δ⁻¹⌉₊≤x→
--       algorithmRealizer.cost (encodeInput G ε δ)+(algorithm (encodeInput G ε δ)).worst weight≤q.eval x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeTyped.instCodecList` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.PhysicalStream.Experiment.worst` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.TreeTyped.weight` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm`, `OAI.MatchingFPRAS.LiteralAlgorithm.algorithmRealizer`, `OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol` and `OAI.MatchingFPRAS.OnlineTree.Realizer` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput`, `OAI.MatchingFPRAS.Symbol` and `OAI.MatchingFPRAS.encodeInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.thm_main` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OriginalCost.lean (declaration OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound)

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
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

lemma algorithm_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) (ε δ : ℚ)
    (_he : 0<ε) (_he1 : ε<1) (_hd : 0≤δ) (x : ℕ),1≤x→
    (encodeInput G ε δ).length≤x→⌈ε⁻¹⌉₊≤x→Nat.clog 2 ⌈δ⁻¹⌉₊≤x→
    algorithmRealizer.cost (encodeInput G ε δ)+(algorithm (encodeInput G ε δ)).worst weight≤q.eval x := by
  sorry
end MatchingFPRAS.LiteralAlgorithm

end OAI
end
