-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_finish_bound_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:14:43.971538+00:00
-- url     : https://prove2.me/theorems/436b46b6-3edd-4b89-9f10-65f7af2313c4
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun`, with `open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight`, `open BinaryPhaseFinish`):
--
--   ```lean
--   lemma finish_bound_s238r {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
--       (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
--       (fuel : ℕ) (t : State m d) (hz : Height t.phase (3*(N+1)^2))
--       (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
--       (finish distance F v lam fuel t).1.phase=t.phase ∧
--       ∀ j : Fin d,(BinaryRational.encode (finish distance F v lam fuel t).1.budget[j]).length ≤ budgetBound.eval N
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.RationalPhase.State` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.RationalHeight.Height` and `OAI.MetricKMedianRecovery.RationalPhase.Event` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalPhase.finish` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.stateBits` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.budgetBound` (definitions bundle `Q238L051` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidBound.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound)

import Mathlib
import Definitions.Def_Q238L051

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
lemma finish_bound_s238r {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (fuel : ℕ) (t : State m d) (hz : Height t.phase (3*(N+1)^2))
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
    (finish distance F v lam fuel t).1.phase=t.phase ∧
    ∀ j : Fin d,(BinaryRational.encode (finish distance F v lam fuel t).1.budget[j]).length ≤ budgetBound.eval N := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end
