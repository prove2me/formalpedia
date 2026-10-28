-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_FiniteTrial_ScaleState_runLaw_tv
-- name    : OAI.MatchingFPRAS.FiniteTrial.ScaleState.runLaw_tv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T17:51:41.923382+00:00
-- url     : https://prove2.me/theorems/05eff5c7-025b-4edd-a848-edafa3e37bbf
-- title:
--   OAI.MatchingFPRAS.FiniteTrial.ScaleState.runLaw_tv: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.FiniteTrial.ScaleState.runLaw_tv` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/GuardProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/GuardProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.FiniteTrial`, with `open Finset Switching Transport Enlargement Adaptive Variation`, `open scoped Classical`):
--
--   ```lean
--   lemma ScaleState.runLaw_tv (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (s : ScaleState G j) :
--       tv (s.runLaw p hj).mass (sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D) ≤
--         3/(1000*p.K*p.S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.Enlargement.SourceMarked`, `OAI.MatchingFPRAS.Enlargement.sourceLaw` and `OAI.MatchingFPRAS.Adaptive.Law` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.FiniteTrial.ScaleState`, `OAI.MatchingFPRAS.Variation.tv` and `OAI.MatchingFPRAS.FiniteTrial.ScaleState.activity` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.Trial.Parameters` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal`, `OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_5`, `OAI.MatchingFPRAS.FiniteTrial.ScaleState.runLaw`, `OAI.MatchingFPRAS.Trial.Parameters.D` and `OAI.MatchingFPRAS.Trial.Parameters.S` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_success` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/GuardProbability.lean (declaration OAI.MatchingFPRAS.FiniteTrial.ScaleState.runLaw_tv)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive Variation
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal_5
lemma ScaleState.runLaw_tv (p : Trial.Parameters G) {j : ℕ} (hj : j ≤ p.K) (s : ScaleState G j) :
    tv (s.runLaw p hj).mass (sourceLaw (fun x y => (s.activity x y : ℝ)) p.K p.D) ≤
      3/(1000*p.K*p.S) := by
  sorry

end MatchingFPRAS.FiniteTrial

end OAI
end
