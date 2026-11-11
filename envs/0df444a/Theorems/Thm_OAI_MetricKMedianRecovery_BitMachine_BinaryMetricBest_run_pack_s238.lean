-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricBest_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:39:58.224183+00:00
-- url     : https://prove2.me/theorems/0bbcf599-5884-436e-a8f7-45ec4aba3eb2
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricCost2.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricCost2.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma run_pack_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
--       run (BinaryRationalBest.pack (context δ D) (BinaryFinSet.encode S) (xs.map BinaryFinSet.encode))=
--         BinaryFinSet.encode (best δ D S xs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.best` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalBest.pack` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.context` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run` (definitions bundle `Q238K026` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.select_bits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.run_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralDispatch.run_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.run_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Repeat.run_source_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryRecovery_run_of_candidates_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.run_source_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySanitizedBest_run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/MetricCost2.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack)

import Mathlib
import Definitions.Def_Q238K026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricBest
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n : ℕ}
lemma run_pack_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (xs : List (Finset (Fin n))) :
    run (BinaryRationalBest.pack (context δ D) (BinaryFinSet.encode S) (xs.map BinaryFinSet.encode))=
      BinaryFinSet.encode (best δ D S xs) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryMetricBest

end OAI
end
