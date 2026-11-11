-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryProjection_run_setBits_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:50:59.265209+00:00
-- url     : https://prove2.me/theorems/9881b441-50bf-425f-9ec8-52d64c798edc
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/ProjectionMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ProjectionMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection`, with `open WordOperations WordList BinaryArithmetic RationalLeaves`, `open BinaryFiniteContext (labels setBits)`):
--
--   ```lean
--   lemma run_setBits_s238 {m : ℕ} (Q : Finset (Label (Fin m))) :
--       run (setBits Q)=BinaryFinSet.encode (RationalLeaves.project Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.project` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run` (definitions bundle `Q238K030` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ProjectionMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits)

import Mathlib
import Definitions.Def_Q238K022
import Definitions.Def_Q238K030

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryProjection
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
lemma run_setBits_s238 {m : ℕ} (Q : Finset (Label (Fin m))) :
    run (setBits Q)=BinaryFinSet.encode (RationalLeaves.project Q) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryProjection

end OAI
end
