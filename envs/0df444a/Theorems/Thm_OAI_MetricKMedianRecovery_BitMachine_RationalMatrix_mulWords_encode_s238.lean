-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_RationalMatrix_mulWords_encode_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:27.638768+00:00
-- url     : https://prove2.me/theorems/ea3ec1f2-0be5-461c-9348-aae866d11a3d
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/Encode2.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/Encode2.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix`, with `open WordOperations BinaryArithmetic`, `open WordList`):
--
--   ```lean
--   lemma mulWords_encode_s238 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
--       mulWords (pairBits (encode A,encode B))=encode (A*B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords` (definitions bundle `Q238K018` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/Encode2.lean (declaration OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList

lemma mulWords_encode_s238 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    mulWords (pairBits (encode A,encode B))=encode (A*B) := by
  sorry
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end
