-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_cutShape_pos_s238r
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.cutShape_pos_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:21:51.202113+00:00
-- url     : https://prove2.me/theorems/668e4de7-30c1-4156-a2b5-463d9fda9dc6
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.cutShape_pos_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.cutShape_pos` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix`, `open scoped Matrix`):
--
--   ```lean
--   lemma cutShape_pos_s238r (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
--       (a : V → ℝ) (ha : a≠0) : (cutShape d H a).PosDef
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.cutShape` (definitions bundle `Q238L004` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.Ellipsoid.advance_pos_lower_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_inverse_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.inflatedShape_lower_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238r`, `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_bounds_s238r` and `OAI.MetricKMedianRecovery.Ellipsoid.stepShape_pos_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.cutShape_pos)

import Mathlib
import Definitions.Def_Q238L004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma cutShape_pos_s238r (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a : V → ℝ) (ha : a≠0) : (cutShape d H a).PosDef := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
