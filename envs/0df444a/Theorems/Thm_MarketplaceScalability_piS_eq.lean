-- Prove2me | Theorems.Thm_MarketplaceScalability_piS_eq
-- name    : MarketplaceScalability.piS_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:23.677744+00:00
-- url     : https://prove2.me/theorems/fb0f6099-8dcc-416d-bc0c-6e53e2a062b1
-- title:
--   Eq. (6) — the scalable profit function (corrected: demand conditions)
-- statement:
--   Let $p_s$ be the cutoff price. For every price $p>0$,
--   $$
--   \pi_S(p)=\begin{cases}\pi_o,&p>p_s,\\ \pi(p),&p\le p_s.\end{cases}
--   $$
--
--   The profit function defined from the sellers' comparison is therefore the source's eq. (6).
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - encoding: p_s denoted as the cutoff price → a point of (0, c̄] with the defining equality, as hypotheses; reason: the theorem on the cutoff price shows these hypotheses pin down one number
--   - encoding: all prices p → prices p > 0; reason: the first-order condition has no solution at p ≤ 0
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, eq. (6), p.9

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_piS

namespace MarketplaceScalability

/-- **Eq. (6), p.9.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: for the cutoff price `p_s`, `π_S(p) = π_o` if `p > p_s`, and
`π_S(p) = π(p)` if `p ≤ p_s`.

**Formalization Note** `p_s` is the point of `cutoff_price`: the hypotheses pin it down uniquely. -/
theorem piS_eq (M : Model) {ps : ℝ} (hps : ps ∈ Set.Ioc 0 M.cbar)
    (hcut : M.sellerPayoff ps M.f = M.sellerPayoff M.cown M.F) {p : ℝ} (hp : 0 < p) :
    M.piS p = if p ≤ ps then M.pi p else M.piO := by sorry

end MarketplaceScalability
