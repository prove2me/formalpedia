-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalSearch_iterate_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:49:49.757207+00:00
-- url     : https://prove2.me/theorems/bbb70433-7265-41b8-a518-0f9ba70bfa19
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalBest.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalBest.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch`, with `open WordOperations WordList BinaryArithmetic RationalLeaves`, `open BinaryFiniteContext (labels setBits)`, `open BinaryOpeningPayment (field field_encode)`):
--
--   ```lean
--   lemma iterate_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w n : ℕ) :
--       (step w)^[n] (pack distance fs S)=pack distance fs
--         (LocalSearch.executableDescent fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w n S)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.LocalSearch.executableDescent` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCost.cost` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.step` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.pack` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Geometry/LocalBest.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack)

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

namespace MetricKMedianRecovery.BitMachine.BinaryLocalSearch
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_encode)
lemma iterate_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Label (Fin m))) (S : Finset (Label (Fin m))) (w n : ℕ) :
    (step w)^[n] (pack distance fs S)=pack distance fs
      (LocalSearch.executableDescent fs (fun T=>⌈BinaryLocalCost.cost distance T⌉₊) w n S) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryLocalSearch

end OAI
end
