-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryTaggedSets_unshift_encode_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:54:14.038987+00:00
-- url     : https://prove2.me/theorems/d11b1939-c7da-4226-82dd-8b7ce25ff944
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FinImages.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FinImages.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets`, with `open WordOperations WordList BinaryArithmetic`):
--
--   ```lean
--   lemma unshift_encode_s238r (S : Finset (Fin n)) :
--       unshift (pairBits (n.bits,BinaryFinSet.encode (S.image right)))=BinaryFinSet.encode S
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.right` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FinImages.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift_encode)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L030

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
lemma unshift_encode_s238r (S : Finset (Fin n)) :
    unshift (pairBits (n.bits,BinaryFinSet.encode (S.image right)))=BinaryFinSet.encode S := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI
end
