-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricAnchor_anchorInput_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:39:57.072368+00:00
-- url     : https://prove2.me/theorems/506245ca-7ad5-4253-a6c1-fd4639efd171
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricAnchor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricAnchor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor`, with `open WordOperations WordList RationalLeaves`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma anchorInput_pack_s238 (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) :
--       anchorInput (pack δ D F r)=BinaryLocalAnchor.pack (fun i j=>δ i (SortedIndex.enum D j)) (F.sort (·≤·)) r
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.SortedIndex.enum` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput` and `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.pack` (definitions bundle `Q238K026` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricAnchor.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack)

import Mathlib
import Definitions.Def_Q238K026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field )
attribute [local irreducible] BinaryMetricArrays.run
variable {n : ℕ}
attribute [local irreducible] WordList.map
attribute [local semireducible] WordList.map
lemma anchorInput_pack_s238 (δ : Fin n→Fin n→ℚ) (D F : Finset (Fin n)) (r : ℕ) :
    anchorInput (pack δ D F r)=BinaryLocalAnchor.pack (fun i j=>δ i (SortedIndex.enum D j)) (F.sort (·≤·)) r := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

end OAI
end
