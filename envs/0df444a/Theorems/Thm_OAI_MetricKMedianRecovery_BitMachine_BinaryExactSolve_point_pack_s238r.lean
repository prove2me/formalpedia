-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_point_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:46:17.384942+00:00
-- url     : https://prove2.me/theorems/9217ce73-646f-47a6-873b-bf6dc37cf52c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix`, `open WordList BinaryRationalDecision RationalMatrix`):
--
--   ```lean
--   lemma point_pack_s238r {n : ℕ} (rs : List (Row n)) (B : ℕ)
--       (hf : ∃ x : Fin n → ℝ, (∀ q∈rs,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
--       point (pack rs B)=rowEncode (facePoint rs B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row.RealHolds` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.facePoint` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.rowEncode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.pack` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack)

import Mathlib
import Definitions.Def_Q238L030

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
lemma point_pack_s238r {n : ℕ} (rs : List (Row n)) (B : ℕ)
    (hf : ∃ x : Fin n → ℝ, (∀ q∈rs,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    point (pack rs B)=rowEncode (facePoint rs B) := by
  sorry
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end
