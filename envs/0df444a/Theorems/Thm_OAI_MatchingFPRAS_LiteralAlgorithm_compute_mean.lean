-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_LiteralAlgorithm_compute_mean
-- name    : OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:08:22.165773+00:00
-- url     : https://prove2.me/theorems/659f33de-61a5-43a3-a15f-b8665ea6d9a6
-- title:
--   OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/Algorithm.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/Algorithm.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.LiteralAlgorithm`, with `open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial`):
--
--   ```lean
--   lemma compute_mean {G : GraphInput} [Nontrivial (Fin G.n)]
--       (hn : 2≤G.n) (hev : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ)
--       (h : Fraction→ℚ) :
--       (compute (parseInput (encodeInput G ε δ))).mean h=
--         PhysicalStream.qaverage (fun b=>h (TreeFraction.repr
--           (FiniteTrial.guardedAmplifiedBitOutput (FiniteTrial.parameters G hn hev ε he he1) δ b)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeFraction.Fraction` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.PhysicalStream.qaverage` and `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.TreeFraction.repr` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.LiteralInput.parseInput` (definitions bundle `OAIQ051M003` of this split); `OAI.MatchingFPRAS.FiniteTrial.guardedAmplifiedBitOutput`, `OAI.MatchingFPRAS.FiniteTrial.guardedAmplifiedBits`, `OAI.MatchingFPRAS.FiniteTrial.parameters` and `OAI.MatchingFPRAS.LiteralAlgorithm.compute` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput` and `OAI.MatchingFPRAS.encodeInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proofs of `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success` and `OAI.MatchingFPRAS.thm_main` of this split import it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/Algorithm.lean (declaration OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean)

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

lemma compute_mean {G : GraphInput} [Nontrivial (Fin G.n)]
    (hn : 2≤G.n) (hev : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ)
    (h : Fraction→ℚ) :
    (compute (parseInput (encodeInput G ε δ))).mean h=
      PhysicalStream.qaverage (fun b=>h (TreeFraction.repr
        (FiniteTrial.guardedAmplifiedBitOutput (FiniteTrial.parameters G hn hev ε he he1) δ b))) := by
  sorry
end MatchingFPRAS.LiteralAlgorithm

end OAI
end
