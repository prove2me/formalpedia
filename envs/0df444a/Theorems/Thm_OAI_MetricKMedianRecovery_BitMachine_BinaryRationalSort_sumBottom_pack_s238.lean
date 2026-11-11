-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRationalSort_sumBottom_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:01:26.36919+00:00
-- url     : https://prove2.me/theorems/d3da19fd-8b54-4b17-b4dd-358bf18877c6
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort`, with `open WordOperations WordList BinaryArithmetic`):
--
--   ```lean
--   lemma sumBottom_pack_s238 {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
--       sumBottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))=
--         BinaryRational.encode (bottomValues v k).sum
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` and `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.bottomValues` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom` (definitions bundle `Q238K037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] mapWith
lemma sumBottom_pack_s238 {r : ℕ} (v : Fin r→ℚ) (k : ℕ) :
    sumBottom (pairBits (k.bits,encode (List.ofFn (fun i=>BinaryRational.encode (v i)))))=
      BinaryRational.encode (bottomValues v k).sum := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end
