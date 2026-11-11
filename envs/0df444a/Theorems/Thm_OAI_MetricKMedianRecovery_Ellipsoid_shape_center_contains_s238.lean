-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_shape_center_contains_s238
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:12:27.537501+00:00
-- url     : https://prove2.me/theorems/69d50847-642e-4e6a-a471-726a389705af
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix`, `open scoped Matrix`):
--
--   ```lean
--   lemma shape_center_contains_s238 (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
--       (a c x : V → ℝ) (ha : a≠0) (t : ℝ)
--       (htlo : Real.sqrt (quad H a)≤t) (hthi : t≤(1+1/(32*d))*Real.sqrt (quad H a))
--       (hx : quad H⁻¹ (x-c)≤1) (hcut : a ⬝ᵥ (x-c)≤0) :
--       quad ((1-1/(8*d^2)) • cutMatrix d H⁻¹ (normalizedDual H a))
--         (x-centerUpdate d H a c t)≤1
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.centerUpdate`, `OAI.MetricKMedianRecovery.Ellipsoid.cutMatrix`, `OAI.MetricKMedianRecovery.Ellipsoid.normalizedDual` and `OAI.MetricKMedianRecovery.Ellipsoid.quad` (definitions bundle `Q238K004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Ellipsoid.iterate_contains_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CenterUpdate.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.shape_center_contains)

import Mathlib
import Definitions.Def_Q238K004

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

lemma shape_center_contains_s238 (d : ℝ) (hd : 1<d) (H : Matrix V V ℝ) (hH : H.PosDef)
    (a c x : V → ℝ) (ha : a≠0) (t : ℝ)
    (htlo : Real.sqrt (quad H a)≤t) (hthi : t≤(1+1/(32*d))*Real.sqrt (quad H a))
    (hx : quad H⁻¹ (x-c)≤1) (hcut : a ⬝ᵥ (x-c)≤0) :
    quad ((1-1/(8*d^2)) • cutMatrix d H⁻¹ (normalizedDual H a))
      (x-centerUpdate d H a c t)≤1 := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
