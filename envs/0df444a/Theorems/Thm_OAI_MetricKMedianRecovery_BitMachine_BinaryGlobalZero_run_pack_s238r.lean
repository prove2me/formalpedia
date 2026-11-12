-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalZero_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:48:01.362283+00:00
-- url     : https://prove2.me/theorems/3793332f-3382-477e-9f2d-ba63c4ab58e8
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalZero.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalZero.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero`, with `open WordOperations WordList LocalSearch`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma run_pack_s238r (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) :
--       run (pack δ D F)=BinaryFinSet.encode (output δ D F hF)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.output` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.zero_bits_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalZero.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalZero.run_pack)

import Mathlib
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalZero
open WordOperations WordList LocalSearch
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma run_pack_s238r (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (hF : F.Nonempty) :
    run (pack δ D F)=BinaryFinSet.encode (output δ D F hF) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryGlobalZero

end OAI
end
