-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_robust_spectral_s238r
-- name    : OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:22:34.092921+00:00
-- url     : https://prove2.me/theorems/22ed8eba-7ef0-4b30-842c-3245f4462358
-- title:
--   OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InflationPos.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InflationPos.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Ellipsoid`, with `open Matrix`, `open scoped Matrix`):
--
--   ```lean
--   lemma robust_spectral_s238r (d : ℝ) (hd : 2≤d) (M R : Matrix V V ℝ) (hM : M.PosDef)
--       (u : V → ℝ) (hu : quad M u=1)
--       (hRlo : (R-(1-1/(8*d^2)) • ((1-1/(8*d^2)) • cutMatrix d M u)).PosSemidef)
--       (hRhi : ((1-1/(8*d^2)) • cutMatrix d M u-R).PosSemidef) :
--       (R-(1/2:ℝ) • M).PosSemidef ∧ ((3:ℝ) • M-R).PosSemidef
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Ellipsoid.cutMatrix` and `OAI.MetricKMedianRecovery.Ellipsoid.quad` (definitions bundle `Q238L004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Ellipsoid.iterate_shape_entry_bound_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InflationPos.lean (declaration OAI.MetricKMedianRecovery.Ellipsoid.robust_spectral)

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

omit [DecidableEq V] in

lemma robust_spectral_s238r (d : ℝ) (hd : 2≤d) (M R : Matrix V V ℝ) (hM : M.PosDef)
    (u : V → ℝ) (hu : quad M u=1)
    (hRlo : (R-(1-1/(8*d^2)) • ((1-1/(8*d^2)) • cutMatrix d M u)).PosSemidef)
    (hRhi : ((1-1/(8*d^2)) • cutMatrix d M u-R).PosSemidef) :
    (R-(1/2:ℝ) • M).PosSemidef ∧ ((3:ℝ) • M-R).PosSemidef := by
  sorry

end MetricKMedianRecovery.Ellipsoid

end OAI
end
