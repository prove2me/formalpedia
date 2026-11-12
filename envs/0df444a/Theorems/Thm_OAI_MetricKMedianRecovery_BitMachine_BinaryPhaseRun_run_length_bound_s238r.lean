-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_run_length_bound_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:18.946137+00:00
-- url     : https://prove2.me/theorems/ca700a69-0982-46fb-91f9-045c3e564156
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun`, with `open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight`, `open BinaryPhaseFinish`):
--
--   ```lean
--   lemma run_length_bound_s238r {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
--       (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
--       (q : ℕ) (hq : q ≤ N) :
--       (stateBits distance F v lam (RationalPhase.run distance F v lam q s).1).length ≤ sizeBound.eval N
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalPhase.State` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.RationalPhase.Instruction` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.RationalPhase.run` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.stateBits` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.sizeBound` (definitions bundle `Q238L043` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseCount.power_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/BidBound.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound)

import Mathlib
import Definitions.Def_Q238L043

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
lemma run_length_bound_s238r {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (q : ℕ) (hq : q ≤ N) :
    (stateBits distance F v lam (RationalPhase.run distance F v lam q s).1).length ≤ sizeBound.eval N := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end
