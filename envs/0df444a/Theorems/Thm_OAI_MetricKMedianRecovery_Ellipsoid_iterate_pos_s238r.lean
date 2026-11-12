-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_pos_s238r
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:27:58.247468+00:00
-- url     : https://prove2.me/theorems/3064ca9e-0c18-4fa8-acb2-33c256986364
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/State.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/State.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix RationalLinearFeasibility`, `open scoped Matrix`):
--
--   ```lean
--   lemma iterate_pos_s238r {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
--       (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (t : ℕ) :
--       (realMatrix (iterate D rows S t).shape).PosDef
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.State` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.realMatrix` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.iterate` (definitions bundle `Q238L009` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r` and `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/State.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.iterate_pos)

import Mathlib
import Definitions.Def_Q238L009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma iterate_pos_s238r {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (t : ℕ) :
    (realMatrix (iterate D rows S t).shape).PosDef := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
