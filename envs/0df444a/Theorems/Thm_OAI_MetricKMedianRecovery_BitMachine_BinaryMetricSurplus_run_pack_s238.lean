-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricSurplus_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:18:07.544572+00:00
-- url     : https://prove2.me/theorems/7f018269-8c37-4e84-b3f3-09ece96591cd
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/MetricSurplus.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/MetricSurplus.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238 (v : ℚ) (C : ℕ) (δ : Fin n→Fin n→ℕ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
--       run v C (pack (fun i j=>(δ i j:ℚ)) D F Δ h L)=
--         BinaryCanonicalSurplus.run v C (BinaryCanonicalSurplus.pack (fun i j=>δ j i) F D Δ h L)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.run` (definitions bundle `Q238K049` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run` (definitions bundle `Q238K051` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.low_candidate_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/MetricSurplus.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryMetricSurplus.run_pack)

import Mathlib
import Definitions.Def_Q238K051

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricSurplus
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n : ℕ}
lemma run_pack_s238 (v : ℚ) (C : ℕ) (δ : Fin n→Fin n→ℕ) (D F : Finset (Fin n)) (Δ h L : ℕ) :
    run v C (pack (fun i j=>(δ i j:ℚ)) D F Δ h L)=
      BinaryCanonicalSurplus.run v C (BinaryCanonicalSurplus.pack (fun i j=>δ j i) F D Δ h L) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryMetricSurplus

end OAI
end
