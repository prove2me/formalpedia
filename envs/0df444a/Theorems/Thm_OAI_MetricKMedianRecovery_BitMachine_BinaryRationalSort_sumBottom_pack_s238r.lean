-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRationalSort_sumBottom_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:58:49.744195+00:00
-- url     : https://prove2.me/theorems/3016b2fc-2149-413b-8675-a2103149360c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort`, with `open WordOperations WordList BinaryArithmetic`):
--
--   ```lean
--   lemma sumBottom_pack_s238r {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
--       sumBottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))=
--         BinaryRational.encode (bottomValues v k).sum
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.bottomValues` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom` (definitions bundle `Q238L034` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] mapWith
lemma sumBottom_pack_s238r {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    sumBottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))=
      BinaryRational.encode (bottomValues v k).sum := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end
