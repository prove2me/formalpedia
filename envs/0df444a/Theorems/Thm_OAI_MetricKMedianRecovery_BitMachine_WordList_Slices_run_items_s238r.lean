-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_WordList_Slices_run_items_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:54:11.223377+00:00
-- url     : https://prove2.me/theorems/4f5bb8e5-5a30-4b0e-a9dd-3f05ca22834e
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/SliceFold.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/SliceFold.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices`, with `open WordOperations CanonicalSlices`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma run_items_s238r {X : Type*} (enc : X → List Bool) (xs : List X) :
--       run (itemsBits enc xs)=outBits enc (CanonicalMergeRefinement.cuts xs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.cuts` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.itemsBits` and `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.outBits` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run` (definitions bundle `Q238L029` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinarySuffix.slices_labels_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/SliceFold.lean (declaration OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items)

import Mathlib
import Definitions.Def_Q238L029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.Slices
open WordOperations CanonicalSlices
open BinaryOpeningPayment (field )

lemma run_items_s238r {X : Type*} (enc : X → List Bool) (xs : List X) :
    run (itemsBits enc xs)=outBits enc (CanonicalMergeRefinement.cuts xs) := by
  sorry
end MetricKMedianRecovery.BitMachine.WordList.Slices

end OAI
end
