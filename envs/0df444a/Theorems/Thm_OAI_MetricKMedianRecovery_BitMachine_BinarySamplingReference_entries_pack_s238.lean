-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingReference_entries_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:13.017023+00:00
-- url     : https://prove2.me/theorems/e5f9771b-09fc-47a9-82ec-ed85de9dfe6f
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingReference.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingReference.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_encode)`, `open BinaryRationalSort (entryBits)`):
--
--   ```lean
--   lemma entries_pack_s238 (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
--       entries (pack Δ A v r row)=encode ((values Δ A v r row).map entryBits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.values` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.entryBits` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.pack` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryBlueRecords_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRows_run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Update_chosen_pair_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingReference.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack)

import Mathlib
import Definitions.Def_Q238K020
import Definitions.Def_Q238K022

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
open BinaryRationalSort (entryBits)
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
lemma entries_pack_s238 (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) :
    entries (pack Δ A v r row)=encode ((values Δ A v r row).map entryBits) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

end OAI
end
