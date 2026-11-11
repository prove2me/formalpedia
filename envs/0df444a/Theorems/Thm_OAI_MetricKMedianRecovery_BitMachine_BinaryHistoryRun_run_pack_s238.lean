-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryHistoryRun_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:11:02.034953+00:00
-- url     : https://prove2.me/theorems/5b5cdca3-df45-472b-933b-510647869481
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/HistoryBits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/HistoryBits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun`, with `open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate`, `open BinaryRunTrace (finished finished_computes )`):
--
--   ```lean
--   lemma run_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
--       (v lam : ℚ) (q : ℕ) (s : State m d) :
--       run (pairBits (List.replicate q true,stateBits distance F v lam s))=
--         pack distance F v lam (RationalPhase.historyRun distance F v lam q s).1 (RationalPhase.historyRun distance F v lam q s).2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalPhase.State` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.RationalPhase.historyRun` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseUpdate.stateBits` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run` (definitions bundle `Q238K043` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/HistoryBits.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryHistoryRun.run_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryHistoryRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
open BinaryRunTrace (finished finished_computes )
attribute [local irreducible] finished finished_computes
attribute [local irreducible] chunk chunk_computes
lemma run_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) :
    run (pairBits (List.replicate q true,stateBits distance F v lam s))=
      pack distance F v lam (RationalPhase.historyRun distance F v lam q s).1 (RationalPhase.historyRun distance F v lam q s).2 := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryHistoryRun

end OAI
end
