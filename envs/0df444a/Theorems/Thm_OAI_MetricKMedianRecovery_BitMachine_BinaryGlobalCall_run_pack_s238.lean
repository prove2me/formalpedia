-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryGlobalCall_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:17:21.877559+00:00
-- url     : https://prove2.me/theorems/9105b120-9f82-484e-84c5-6b4b29f76171
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalCall.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalCall.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238 (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
--       run v C Q d (pack I M raw)=BinaryTaggedSets.unshift (pairBits (I.pointCount.bits,
--         A.run v C Q d (integralPack I M (raw.take ((A.budget Q).eval (integralPack I M []).length)))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.integralPack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryTaggedSets.unshift` (definitions bundle `Q238K031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.budget` (definitions bundle `Q238K051` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.A.run` (definitions bundle `Q238K053` of this split); `OAI.MetricKMedianRecovery.RationalMetricInput` and `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalOuter.finite_program_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalRounding.rounded_program_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Algorithms/GlobalCall.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.run_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K053

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] counter demand base RawTake.run UnaryResources.lengthBits
attribute [local irreducible] call BinaryIntegralAll.run BinaryIntegralDispatch.budget ready norm src clamp BinaryInputParser.Metric.count
lemma run_pack_s238 (v : ℚ) (C : ℕ) (Q : Polynomial ℕ) (d : ℕ) (I : RationalMetricInput) (M : ℚ) (raw : List Bool) :
    run v C Q d (pack I M raw)=BinaryTaggedSets.unshift (pairBits (I.pointCount.bits,
      A.run v C Q d (integralPack I M (raw.take ((A.budget Q).eval (integralPack I M []).length))))) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end
