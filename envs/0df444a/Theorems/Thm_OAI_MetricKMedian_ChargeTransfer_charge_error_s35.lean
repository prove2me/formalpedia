-- Prove2me | Theorems.Thm_OAI_MetricKMedian_ChargeTransfer_charge_error_s35
-- name    : OAI.MetricKMedian.ChargeTransfer.charge_error_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:34:06.505284+00:00
-- url     : https://prove2.me/theorems/70beaef6-7231-41fe-baba-607f7b0d9a7f
-- title:
--   OAI.MetricKMedian.ChargeTransfer.charge_error_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.ChargeTransfer`):
--
--   ```lean
--   theorem charge_error_s35 {p q a b k H x w r e : ℝ}
--       (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
--       (ha0 : 1 ≤ a) (ha : a ≤ 2) (hb0 : 1 ≤ b) (hb : b ≤ 2)
--       (hk0 : 0 ≤ k) (hk : k ≤ 1/5) (hH0 : 0 ≤ H) (hH : H ≤ 2/5)
--       (hx0 : 0 ≤ x) (hw0 : 0 ≤ w) (hxw : x+w ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1)
--       (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
--       |charge p a k H x w r s-charge q b k H x w r s| ≤ 25*e*(r+w^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.ChargeTransfer.charge` (definitions bundle `OAIQ035K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ChargeTransfer

theorem charge_error_s35 {p q a b k H x w r e : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
    (ha0 : 1 ≤ a) (ha : a ≤ 2) (hb0 : 1 ≤ b) (hb : b ≤ 2)
    (hk0 : 0 ≤ k) (hk : k ≤ 1/5) (hH0 : 0 ≤ H) (hH : H ≤ 2/5)
    (hx0 : 0 ≤ x) (hw0 : 0 ≤ w) (hxw : x+w ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1)
    (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
    |charge p a k H x w r s-charge q b k H x w r s| ≤ 25*e*(r+w^2) := by
  sorry

end MetricKMedian.ChargeTransfer

end
end

end OAI
end
