-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryOpeningNearest_run_source_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:50:36.288454+00:00
-- url     : https://prove2.me/theorems/9e44434e-00c3-427b-a675-0682deb363fc
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Values.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Values.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest`, with `open WordOperations BinaryArithmetic WordList BinaryOpeningActivity`):
--
--   ```lean
--   lemma run_source_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
--       (j : Fin d) (W : Finset (Fin m)) :
--       run (pairBits (context distance v z j,
--         indices ((EffectiveOpenability.subtypeList W).map Subtype.val)))=
--         BinaryRational.encode (RationalOpenability.nearest distance W j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.EffectiveOpenability.subtypeList` and `OAI.MetricKMedianRecovery.RationalOpenability.nearest` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run` (definitions bundle `Q238L015` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.indices` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.context` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.summand_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Values.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningNearest
open WordOperations BinaryArithmetic WordList BinaryOpeningActivity

lemma run_source_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v z : ℚ)
    (j : Fin d) (W : Finset (Fin m)) :
    run (pairBits (context distance v z j,
      indices ((EffectiveOpenability.subtypeList W).map Subtype.val)))=
      BinaryRational.encode (RationalOpenability.nearest distance W j) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryOpeningNearest

end OAI
end
