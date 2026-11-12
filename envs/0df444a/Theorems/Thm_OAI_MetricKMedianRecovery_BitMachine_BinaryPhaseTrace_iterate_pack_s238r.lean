-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseTrace_iterate_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:58:58.063279+00:00
-- url     : https://prove2.me/theorems/52111c48-a1e8-422e-b5d2-df6566abf798
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack11.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack11.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace`, with `open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate`, `open BinaryPhaseFinish`):
--
--   ```lean
--   lemma iterate_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
--       (v lam : ℚ) (fuel : ℕ) (s : State m d) (es : List (Event m d)) :
--       step^[fuel] (pack distance F v lam s es)=
--         pack distance F v lam (finish distance F v lam fuel s).1 ((finish distance F v lam fuel s).2.reverse++es)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalPhase.State` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.RationalPhase.Event` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalPhase.finish` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.step` (definitions bundle `Q238L033` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_length_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack11.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack)

import Mathlib
import Definitions.Def_Q238L030
import Definitions.Def_Q238L033

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseTrace
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryPhaseFinish
lemma iterate_pack_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (fuel : ℕ) (s : State m d) (es : List (Event m d)) :
    step^[fuel] (pack distance F v lam s es)=
      pack distance F v lam (finish distance F v lam fuel s).1 ((finish distance F v lam fuel s).2.reverse++es) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryPhaseTrace

end OAI
end
