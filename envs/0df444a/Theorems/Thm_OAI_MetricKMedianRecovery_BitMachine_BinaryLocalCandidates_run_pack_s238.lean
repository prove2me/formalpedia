-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalCandidates_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:49:39.821263+00:00
-- url     : https://prove2.me/theorems/b0335282-905d-43a5-8c5c-63b6d90b9750
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalCandidates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalCandidates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates`, with `open WordOperations WordList BinaryArithmetic RationalLeaves`, `open BinaryFiniteContext (labels setBits)`, `open BinaryLocalSets`):
--
--   ```lean
--   lemma run_pack_s238 {m : ℕ} (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w : ℕ) :
--       run w (pairBits (labels fs,setBits S))=encode ((LocalSearch.exchangeList fs S w).map setBits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.LocalSearch.exchangeList` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.labels` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run` (definitions bundle `Q238K030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_step_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalCandidates.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K030

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCandidates
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryLocalSets
lemma run_pack_s238 {m : ℕ} (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w : ℕ) :
    run w (pairBits (labels fs,setBits S))=encode ((LocalSearch.exchangeList fs S w).map setBits) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryLocalCandidates

end OAI
end
