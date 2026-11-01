-- Prove2me | Theorems.Thm_OAI_MetricKMedian_ChargeTransfer_charge_error_s53
-- name    : OAI.MetricKMedian.ChargeTransfer.charge_error_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:33:06.836737+00:00
-- url     : https://prove2.me/theorems/4eb2915c-4e9a-4056-b28d-bb03258d8c75
-- title:
--   OAI.MetricKMedian.ChargeTransfer.charge_error_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.ChargeTransfer.charge_error` of [lean/OAI/Combinatorics/KMedian/Analysis/ChargeTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ChargeTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.ChargeTransfer`):
--
--   ```lean
--   theorem charge_error_s53 {p q a b k H x w r e : ℝ}
--       (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hq0 : 0 ≤ q) (hq : q ≤ 1/2)
--       (ha0 : 1 ≤ a) (ha : a ≤ 2) (hb0 : 1 ≤ b) (hb : b ≤ 2)
--       (hk0 : 0 ≤ k) (hk : k ≤ 1/5) (hH0 : 0 ≤ H) (hH : H ≤ 2/5)
--       (hx0 : 0 ≤ x) (hw0 : 0 ≤ w) (hxw : x+w ≤ 1) (hr0 : 0 ≤ r) (hr : r ≤ 1)
--       (hpq : |p-q| ≤ e) (hab : |a-b| ≤ 2*e) (s : Bool) :
--       |charge p a k H x w r s-charge q b k H x w r s| ≤ 25*e*(r+w^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.ChargeTransfer.charge` (definitions bundle `OAIQ053K002` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/ChargeTransfer.lean (declaration OAI.MetricKMedian.ChargeTransfer.charge_error)

import Mathlib
import Definitions.Def_OAIQ053K002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ChargeTransfer

theorem charge_error_s53 {p q a b k H x w r e : ℝ}
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
