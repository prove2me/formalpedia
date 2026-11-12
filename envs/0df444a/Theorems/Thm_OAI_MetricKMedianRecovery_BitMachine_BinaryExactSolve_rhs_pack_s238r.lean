-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_rhs_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:46:15.012102+00:00
-- url     : https://prove2.me/theorems/34f0f069-8758-4406-9e53-92779e3dc941
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix`, `open WordList BinaryRationalDecision RationalMatrix`):
--
--   ```lean
--   lemma rhs_pack_s238r {n : ℕ} (rs : List (Row n)) (B : ℕ) :
--       rhs (pack rs B)=rowEncode ((rowMatrix (finalFace rs B)).transpose *ᵥ rowBounds (finalFace rs B))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.finalFace` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.rowBounds` and `OAI.MetricKMedianRecovery.Ellipsoid.rowMatrix` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.rowEncode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.pack` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack)

import Mathlib
import Definitions.Def_Q238L030

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
lemma rhs_pack_s238r {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    rhs (pack rs B)=rowEncode ((rowMatrix (finalFace rs B)).transpose *ᵥ rowBounds (finalFace rs B)) := by
  sorry
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end
