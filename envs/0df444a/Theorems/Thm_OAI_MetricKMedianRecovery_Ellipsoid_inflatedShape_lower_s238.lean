-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_inflatedShape_lower_s238
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:12.901203+00:00
-- url     : https://prove2.me/theorems/60fd01a6-93f9-43fe-968f-6194bf3d6a7a
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FormTrans.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FormTrans.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix`, `open scoped Matrix`):
--
--   ```lean
--   lemma inflatedShape_lower_s238 (H : Matrix V V ℚ) (a : V → ℚ) (hn : 2≤Fintype.card V)
--       (hH : (realMatrix H).PosDef) (ha : a≠0) :
--       (realMatrix (rationalInflatedShape H a)-(1/3:ℝ) • realMatrix H).PosSemidef
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.rationalInflatedShape` and `OAI.MetricKMedianRecovery.Ellipsoid.realMatrix` (definitions bundle `Q238K004` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.Ellipsoid.advance_pos_lower_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_s238` and `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FormTrans.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower)

import Mathlib
import Definitions.Def_Q238K004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

section
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma inflatedShape_lower_s238 (H : Matrix V V ℚ) (a : V → ℚ) (hn : 2≤Fintype.card V)
    (hH : (realMatrix H).PosDef) (ha : a≠0) :
    (realMatrix (rationalInflatedShape H a)-(1/3:ℝ) • realMatrix H).PosSemidef := by
  sorry

end

open Matrix
open scoped Matrix

end MetricKMedianRecovery.Ellipsoid

end OAI
end
