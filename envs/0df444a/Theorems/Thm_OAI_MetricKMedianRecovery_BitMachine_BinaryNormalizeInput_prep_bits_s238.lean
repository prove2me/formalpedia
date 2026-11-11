-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNormalizeInput_prep_bits_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:57.02932+00:00
-- url     : https://prove2.me/theorems/3fa5c109-bc0b-4a5c-b2cc-f9ce5d1ab276
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma prep_bits_s238 (I : RationalMetricInput) (M : ℚ) :
--       prep (pairBits (I.bits,BinaryRational.encode M))=BinaryNormalization.pack I.distance I.clients.card M
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalization.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep` (definitions bundle `Q238K040` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput`, `OAI.MetricKMedianRecovery.pairBits` and `OAI.MetricKMedianRecovery.RationalMetricInput.bits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.demand_bound_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/NormalizeInput.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryNormalizeInput.prep_bits)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K040

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNormalizeInput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] P.points P.clients P.facilities
  BinaryInputParser.Metric.matrix BinaryInputParser.Metric.count BinaryInputParser.Metric.budget
  BinaryNormalization.run BinaryNormalization.cap BinaryNormalization.mesh
lemma prep_bits_s238 (I : RationalMetricInput) (M : ℚ) :
    prep (pairBits (I.bits,BinaryRational.encode M))=BinaryNormalization.pack I.distance I.clients.card M := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryNormalizeInput

end OAI
end
