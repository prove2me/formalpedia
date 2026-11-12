-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidCut_shapeWords_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:45:36.286096+00:00
-- url     : https://prove2.me/theorems/51fbcf54-6635-4512-a652-2d82f851c28e
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack6.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack6.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut`, with `open WordOperations BinaryArithmetic`, `open scoped Matrix`):
--
--   ```lean
--   lemma shapeWords_pack_s238r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
--       shapeWords (pack H a c D)=RationalMatrix.encode (Ellipsoid.rationalStepShape D H a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.rationalStepShape` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords` (definitions bundle `Q238L014` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.encode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.pack` (definitions bundle `Q238L029` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack6.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack)

import Mathlib
import Definitions.Def_Q238L029

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open scoped Matrix
namespace BinaryEllipsoidCut
lemma shapeWords_pack_s238r {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) (D : ℕ) :
    shapeWords (pack H a c D)=RationalMatrix.encode (Ellipsoid.rationalStepShape D H a) := by
  sorry
end BinaryEllipsoidCut
end MetricKMedianRecovery.BitMachine

end OAI
end
