-- Prove2me | Theorems.Thm_MarketplaceScalability_price_comparison
-- name    : MarketplaceScalability.price_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:12.751886+00:00
-- url     : https://prove2.me/theorems/1a1f38d4-fbc3-47fd-839b-d116093ae665
-- title:
--   Proof of Proposition 1 — the price comparison for (b) (corrected: demand conditions)
-- statement:
--   Let $p_s$ be the cutoff price, let $p_S$ maximize $\pi$ on $(0,p_s]$ and let $p_N$ maximize $\pi$ on $(0,\bar c]$. Then
--   $$
--   p_S\le p_N,
--   $$
--   and $p_S=p_N$ when $p_N\le p_s$.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - reading: any price chosen in the scalable scenario would have been chosen in the non-scalable scenario → p_S = p_N when p_N ≤ p_s, and p_S ≤ p_N always; reason: taken literally the sentence is false when p_s < p_N; the page's conclusion is "weakly higher"
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, proof of Proposition 1, p.26

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_pi

namespace MarketplaceScalability

/-- **The price comparison for (b), proof of Proposition 1, p.26.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "(b) When the platform service
is provided, any price chosen in the scalable scenario would have been chosen in the non-scalable
scenario. If not, there exists a price on [p_s, c̄] which yields an even higher profit, and hence the
optimal price in the non-scalable scenario is weakly higher than that in the scalable scenario."

If `p_S` maximizes `π` on `(0, p_s]` and `p_N` maximizes it on `(0, c̄]`, then `p_S ≤ p_N`, and the two
coincide when `p_N ≤ p_s`.

**Formalization Note** The page's first sentence holds when the non-scalable optimum is available in the
scalable scenario, that is, when `p_N ≤ p_s`; otherwise `p_S ≠ p_N` is possible. -/
theorem price_comparison (M : Model) {ps : ℝ} (hps : ps ∈ Set.Ioc 0 M.cbar)
    (hcut : M.sellerPayoff ps M.f = M.sellerPayoff M.cown M.F) {pS pN : ℝ}
    (hpS : pS ∈ Set.Ioc 0 ps) (hS : IsMaxOn M.pi (Set.Ioc 0 ps) pS)
    (hpN : pN ∈ Set.Ioc 0 M.cbar) (hN : IsMaxOn M.pi (Set.Ioc 0 M.cbar) pN) :
    pS ≤ pN ∧ (pN ≤ ps → pS = pN) := by sorry

end MarketplaceScalability
