-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidIteration_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:45:46.287513+00:00
-- url     : https://prove2.me/theorems/d860e10f-c804-47bc-9279-89bc3ba9d060
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack7.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack7.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight`, `open RationalMatrix BinaryEllipsoidAdvance`):
--
--   ```lean
--   lemma run_pack_s238r (n T R : ℕ) (rs : List (Row n)) (hn : 2≤ n) (hR : 1≤ R) :
--       run (pack n T R rs)=BinaryEllipsoidAdvance.pack (gridDenominator n T) rs
--         (Ellipsoid.iterate (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ)) T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.gridDenominator` and `OAI.MetricKMedianRecovery.Ellipsoid.initialState` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.iterate` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.pack` (definitions bundle `Q238L029` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack7.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack)

import Mathlib
import Definitions.Def_Q238L029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

lemma run_pack_s238r (n T R : ℕ) (rs : List (Row n)) (hn : 2≤ n) (hR : 1≤ R) :
    run (pack n T R rs)=BinaryEllipsoidAdvance.pack (gridDenominator n T) rs
      (Ellipsoid.iterate (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ)) T) := by
  sorry
end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end
