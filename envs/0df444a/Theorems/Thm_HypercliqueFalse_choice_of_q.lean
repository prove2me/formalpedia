-- Prove2me | Theorems.Thm_HypercliqueFalse_choice_of_q
-- name    : HypercliqueFalse.choice_of_q
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:29:58.571737+00:00
-- url     : https://prove2.me/theorems/4e61fa16-7025-41be-bddc-f017e8e6019a
-- title:
--   Proof of Theorem 2.1 — the choice $q = 2^{\lceil (2/\delta)\log_2(1/\delta)\rceil}$ gives $\epsilon \ge \delta^2/(6\log_2(1/\delta))$
-- statement:
--   Let $0 < \delta \le 1/8$ and $q = 2^{\lceil (2/\delta)\log_2(1/\delta)\rceil}$. Then
--   $$
--   (2/q)^{\delta} = 2^{-\delta(\log_2 q - 1)} \le 2^{\delta}\delta^2 \le \delta/4, \qquad \log_2\big(1 + (2/q)^\delta\big) \le \delta/2, \qquad \log_2 q \le (3/\delta)\log_2(1/\delta),
--   $$
--   and consequently
--   $$
--   \frac{\delta - \log_2(1 + (2/q)^\delta)}{\log_2 q} \ \ge\ \frac{\delta^2}{6\log_2(1/\delta)}.
--   $$
--
--   Combined with the potential calculation, this is the saving $\epsilon$ of the recursion in the inductive step of Theorem 2.1.
--
--   Differences from the source:
--   - encoding: q = 2^{⌈(2/δ) log₂(1/δ)⌉} → q : ℕ with q = 2 ^ ⌈(2/δ)·log₂(1/δ)⌉₊ (Nat.ceil); reason: the ceiling of a positive real; same q
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Theorem 2.1, p.13

import Mathlib

set_option autoImplicit false

namespace HypercliqueFalse

/-- **The choice of `q`.** Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), proof of Theorem 2.1, p.13: "We therefore set
q = 2^{⌈(2/δ) log₂(1/δ)⌉}. Since δ ≤ 1/8, we have (2/q)^δ = 2^{−δ(log₂ q−1)} ≤ 2^δδ² ≤ δ/4, and thus
log₂(1 + (2/q)^δ) ≤ δ/2. Together with log₂ q ≤ (3/δ) log₂(1/δ), this gives ϵ ≥ δ²/(6 log₂(1/δ))",
where `ϵ ≥ (δ − log₂(1 + (2/q)^δ))/log₂ q` (same page).

**Formalization Note.** `q` is the natural number `2 ^ ⌈(2/δ) log₂(1/δ)⌉₊` (the ceiling of a positive
real); `log₂` is `Real.logb 2`. -/
theorem choice_of_q (δ : ℝ) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (q : ℕ)
    (hq : q = 2 ^ ⌈(2 / δ) * Real.logb 2 (1 / δ)⌉₊) :
    (2 / (q : ℝ)) ^ δ = (2 : ℝ) ^ (-δ * (Real.logb 2 q - 1)) ∧
      (2 : ℝ) ^ (-δ * (Real.logb 2 q - 1)) ≤ (2 : ℝ) ^ δ * δ ^ 2 ∧
      (2 : ℝ) ^ δ * δ ^ 2 ≤ δ / 4 ∧
      Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ) ≤ δ / 2 ∧
      Real.logb 2 q ≤ 3 / δ * Real.logb 2 (1 / δ) ∧
      δ ^ 2 / (6 * Real.logb 2 (1 / δ)) ≤
        (δ - Real.logb 2 (1 + (2 / (q : ℝ)) ^ δ)) / Real.logb 2 q := by sorry

end HypercliqueFalse
