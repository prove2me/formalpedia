-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLength_view_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:49:26.441208+00:00
-- url     : https://prove2.me/theorems/95e31e00-6203-49a6-8afa-191ebe759b0f
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/LengthCandidates.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LengthCandidates.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryLength`, with `open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement`, `open BinaryFiniteContext (labels setBits)`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma view_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
--       (R H G : List (Label (Fin m))) : view (ctxBits distance F R H G)=
--         Find.optionEncode ((CanonicalLengthView.view (rows distance) F R H G).map planBits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.Find.optionEncode` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.CanonicalLengthView.view` and `OAI.MetricKMedianRecovery.RationalLeaves.rows` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.planBits` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.ctxBits` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LengthCandidates.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack)

import Mathlib
import Definitions.Def_Q238L029
import Definitions.Def_Q238L030

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] WordList.mapWith
lemma view_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Label (Fin m)))
    (R H G : List (Label (Fin m))) : view (ctxBits distance F R H G)=
      Find.optionEncode ((CanonicalLengthView.view (rows distance) F R H G).map planBits) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end
