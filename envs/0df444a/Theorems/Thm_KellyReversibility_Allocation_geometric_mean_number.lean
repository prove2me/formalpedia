-- Prove2me | Theorems.Thm_KellyReversibility_Allocation_geometric_mean_number
-- name    : KellyReversibility.Allocation.geometric_mean_number
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:50:06.076769+00:00
-- url     : https://prove2.me/theorems/4849f0f3-fdce-49b5-94f5-f30699f9f74f
-- title:
--   p. 97 — the geometric law (4.1) has mean a_j/(φ_j − a_j)
-- statement:
--   Let $a > 0$ be the average arrival rate at a channel and $\phi > a$ its capacity. Under the equilibrium distribution (4.1),
--   $$P(n = k) = \Big(1 - \frac{a}{\phi}\Big)\Big(\frac{a}{\phi}\Big)^k, \qquad k = 0, 1, 2, \dots,$$
--   the mean number of customers at the channel is
--   $$\sum_{k=0}^{\infty} k\Big(1 - \frac{a}{\phi}\Big)\Big(\frac{a}{\phi}\Big)^k = \frac{a}{\phi - a},$$
--   the series being convergent.
--
--   This identity is what turns the queueing model of §4.1 into the deterministic objective $\sum_j a_j/(\phi_j - a_j)$ minimized in Theorem 4.1.
--
--   **Formalization Note** The statement asserts convergence and value together (`HasSum`), so the unconditional sum cannot default to $0$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 96, Eq. (4.1), and p. 97, first sentence of the second paragraph

import Mathlib

namespace KellyReversibility.Allocation

theorem geometric_mean_number (a φ : ℝ) (ha : 0 < a) (haφ : a < φ) :
    HasSum (fun n : ℕ => (n : ℝ) * ((1 - a / φ) * (a / φ) ^ n)) (a / (φ - a)) := by sorry

end KellyReversibility.Allocation
