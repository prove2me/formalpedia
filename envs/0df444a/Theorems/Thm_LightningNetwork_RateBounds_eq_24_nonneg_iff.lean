-- Prove2me | Theorems.Thm_LightningNetwork_RateBounds_eq_24_nonneg_iff
-- name    : LightningNetwork.RateBounds.eq_24_nonneg_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:55:18.123887+00:00
-- url     : https://prove2.me/theorems/c5e694f8-d659-4890-be2f-49e2d75ebe3f
-- title:
--   Proof of Theorem 2(ii): (24) is nonnegative iff $C \le 3(B\kappa^4/4)^{1/3} - (B/12)\kappa^2$ (corrected: “positive” → “nonnegative”)
-- statement:
--   Let $B \ge 0$, $\kappa > 0$ and $C \in \mathbb R$. Then
--
--   $$
--   3\left(\frac{2B}{\kappa^2}\right)^{1/3} - \frac B6 - \frac{2C}{\kappa^2} \;\ge\; 0
--   \quad\Longleftrightarrow\quad
--   C \;\le\; 3\left(\frac{B\kappa^4}{4}\right)^{1/3} - \frac{B}{12}\kappa^2 .
--   $$
--
--   Since (24) is a strict lower bound for the excess cost (21), the right-hand condition makes on-chain settlement strictly cheaper than any symmetric channel; its negation is the bound (6) of Theorem 2(ii).
--
--   The paper states “positive if and only if $C \le \dots$”, which fails when $C$ equals the threshold: for $B = 1$, $\kappa = 1$, $C = 3\cdot 4^{-1/3} - 1/12 \approx 1.81$, the quantity (24) is $0$.
--
--   Differences from the source:
--   - correction: (24) is positive if and only if C ≤ 3(Bκ⁴/4)^{1/3} − (B/12)κ² → (24) is nonnegative if and only if C ≤ 3(Bκ⁴/4)^{1/3} − (B/12)κ²; reason: false at equality: B = 1, κ = 1 (e.g. λ = 1, r = 2(cosh 1 − 1)), C = 3·4^{−1/3} − 1/12 > 0 gives (24) = 3·2^{1/3} − 1/6 − 2C = 0, which is not positive
--   - encoding: κ = log(1 + r/λ) with λ, r > 0 → κ is a real parameter, positive or bounded below by a positive quantity; reason: r/λ ↦ log(1 + r/λ) is a bijection of (0, ∞) onto (0, ∞), so the instances are the same
--   - generalization: B > 0 (the cost of resetting a channel) → B ≥ 0; reason: at B = 0 both sides read C ≤ 0; the statement specializes to B > 0
--   - generalization: C > 0 (the cost of an on-chain transaction) → C any real number; reason: the equivalence is an algebraic identity in C
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Channels, Management Science (2023), doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), p. 12

import Mathlib

namespace LightningNetwork.RateBounds

/-- **The sign of (24) (corrected: "positive" → "nonnegative").**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Channels*, Management Science (2023),
doi:10.1287/mnsc.2022.01664, proof of Theorem 2(ii), p. 12: "Thus, this quantity is positive if and only if
C ≤ 3(Bκ⁴/4)^{1/3} − (B/12)κ², which is thus a sufficient condition for the stream of
transactions to be cheaper on-chain than over the channel."

For `B ≥ 0`, `κ > 0` and any `C`:
`3(2B/κ²)^{1/3} − B/6 − 2C/κ² ≥ 0` if and only if `C ≤ 3(Bκ⁴/4)^{1/3} − (B/12)κ²`.

**Formalization Note (correction).** The page says "positive if and only if C ≤ …", which is
false at equality: for `B = 1`, `κ = 1`, `C = 3·4^{−1/3} − 1/12 > 0` the quantity (24) equals `0`.
The statement keeps the printed threshold and its `≤` and reads "positive" as "nonnegative". -/
theorem eq_24_nonneg_iff (B C κ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) :
    0 ≤ 3 * (2 * B / κ ^ 2) ^ (1 / 3 : ℝ) - B / 6 - 2 * C / κ ^ 2 ↔
      C ≤ 3 * (B * κ ^ 4 / 4) ^ (1 / 3 : ℝ) - B / 12 * κ ^ 2 := by sorry

end LightningNetwork.RateBounds
