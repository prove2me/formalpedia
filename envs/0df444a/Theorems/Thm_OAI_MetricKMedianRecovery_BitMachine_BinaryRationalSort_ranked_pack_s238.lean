-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRationalSort_ranked_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:27:39.372218+00:00
-- url     : https://prove2.me/theorems/c4480976-3178-4a88-b4ab-c6232fa07168
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalSort.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalSort.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort`, with `open WordOperations WordList BinaryArithmetic`):
--
--   ```lean
--   lemma ranked_pack_s238 {r : ℕ} (v : Fin r→ℚ) :
--       ranked (encode (List.ofFn (fun i=>BinaryRational.encode (v i))))=encode (List.ofFn (fun i=>entryBits (ranking v i)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` and `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranking` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.entryBits` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/RationalSort.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack)

import Mathlib
import Definitions.Def_Q238K020
import Definitions.Def_Q238K022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

lemma ranked_pack_s238 {r : ℕ} (v : Fin r→ℚ) :
    ranked (encode (List.ofFn (fun i=>BinaryRational.encode (v i))))=encode (List.ofFn (fun i=>entryBits (ranking v i))) := by
  sorry
attribute [local irreducible] ranked
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end
