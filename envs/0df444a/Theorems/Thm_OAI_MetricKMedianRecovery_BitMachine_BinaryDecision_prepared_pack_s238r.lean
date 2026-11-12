-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_prepared_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:45:27.974836+00:00
-- url     : https://prove2.me/theorems/d869a8fe-5afc-466b-8fa3-bf1ff4668afe
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundOp.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundOp.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid`, `open WordList RationalMatrix`):
--
--   ```lean
--   lemma prepared_pack_s238r {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
--       prepared (pack A b B H)=BinaryWeakSolve.pack n (precisionLog m n H) (radiusLog n B) (n*(B+1))
--         (relaxedRows (gapEpsilon m n H) (boundedRows A b B))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.gapEpsilon`, `OAI.MetricKMedianRecovery.Ellipsoid.precisionLog` and `OAI.MetricKMedianRecovery.Ellipsoid.radiusLog` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.boundedRows` and `OAI.MetricKMedianRecovery.Ellipsoid.relaxedRows` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryWeakSolve.pack` (definitions bundle `Q238L031` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/BoundOp.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack)

import Mathlib
import Definitions.Def_Q238L029
import Definitions.Def_Q238L031

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryDecision
open WordList RationalMatrix

lemma prepared_pack_s238r {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (B H : ℕ) :
    prepared (pack A b B H)=BinaryWeakSolve.pack n (precisionLog m n H) (radiusLog n B) (n*(B+1))
      (relaxedRows (gapEpsilon m n H) (boundedRows A b B)) := by
  sorry
end BinaryDecision
end
open WordOperations BinaryArithmetic
end MetricKMedianRecovery.BitMachine

end OAI
end
