-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFinish_finish_length_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:08:15.488348+00:00
-- url     : https://prove2.me/theorems/8c7542a5-64a1-4d4f-9de3-f7cb79a266ed
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidPoly.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidPoly.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish`, with `open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate`):
--
--   ```lean
--   lemma finish_length_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
--       (v lam : ℚ) (s : State m d) (fuel : ℕ) :
--       (stateBits distance F v lam (finish distance F v lam fuel s).1).length ≤
--         capPoly.eval (stateBits distance F v lam s).length
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalPhase.State` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.RationalPhase.Event` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalPhase.finish` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.stateBits` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.capPoly` (definitions bundle `Q238L039` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_length_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidPoly.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length)

import Mathlib
import Definitions.Def_Q238L039

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
lemma finish_length_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (fuel : ℕ) :
    (stateBits distance F v lam (finish distance F v lam fuel s).1).length ≤
      capPoly.eval (stateBits distance F v lam s).length := by
  sorry

end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end
