-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_shape_entry_bound_s238r
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:28:29.819472+00:00
-- url     : https://prove2.me/theorems/05ce2a54-4ca9-4a0e-a382-ab7331c0125a
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Grid.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Grid.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix RationalLinearFeasibility`, `open scoped Matrix`):
--
--   ```lean
--   lemma iterate_shape_entry_bound_s238r (n T R : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
--       (t : ℕ) (ht : t≤T) (i j : Fin n) :
--       |(iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j|≤(2:ℚ)^t*(R:ℚ)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.gridDenominator`, `OAI.MetricKMedianRecovery.Ellipsoid.initialState` and `OAI.MetricKMedianRecovery.Ellipsoid.State` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.iterate` (definitions bundle `Q238L009` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Grid.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound)

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

lemma iterate_shape_entry_bound_s238r (n T R : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
    (t : ℕ) (ht : t≤T) (i j : Fin n) :
    |(iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j|≤(2:ℚ)^t*(R:ℚ)^2 := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
