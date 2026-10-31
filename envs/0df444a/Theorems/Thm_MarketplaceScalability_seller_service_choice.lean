-- Prove2me | Theorems.Thm_MarketplaceScalability_seller_service_choice
-- name    : MarketplaceScalability.seller_service_choice
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:43.975366+00:00
-- url     : https://prove2.me/theorems/3640801b-dcd6-4ef4-86b7-0ecd96f3fc2b
-- title:
--   §2.4, §3.1 — what Assumption 1 implies for sellers' service choice (corrected: demand conditions)
-- statement:
--   1. Sellers enter under the market service, and under the platform service at every price $p\in(0,\bar c]$: their payoff is positive.
--   2. Sellers who can scale prefer own service to the market service.
--   3. On $(0,\bar c]$ the payoff $p\mapsto(1-\alpha)R(q(p))-pq(p)-f$ is strictly decreasing, so at these prices the platform service is at least as good as the market.
--   4. For $p>\bar c$ the market strictly beats the platform service: at every output $x\in J$,
--   $$
--   (1-\alpha)R(x)-p\,x-f<(1-\alpha)R(q_m)-\bar c\,q_m-f.
--   $$
--
--   Together these give the sellers' entry and service stage of the game, and in particular the case distinction at $p=\bar c$ in (4).
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - encoding: platform service used only when p ≤ c̄ → for p > c̄ a comparison at every output x ∈ J; reason: q(p) is not meaningful above c̄ under the corrected conditions; no instance changes
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §2.4, p.7; §3.1, p.8

import Mathlib
import Definitions.Def_MarketplaceScalability_Model

namespace MarketplaceScalability

/-- **Sellers' service choice, pp.7–8.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §2.4, p.7, on Assumption 1, and §3.1, p.8: "Note
that the high-type sellers will use the platform service only when p ≤ c̄, which is the market
price."

1. Sellers enter under the market service, and under the platform service at any `p ∈ (0, c̄]`.
2. Scalable sellers prefer own service to the market service.
3. `p ↦` the payoff at `(p, f)` is strictly decreasing on `(0, c̄]`, so on this range the platform service
   is weakly preferred to the market.
4. For `p > c̄` the market strictly beats the platform service at every output in `J`.

**Formalization Note** Part 4 quantifies over outputs because `q p` is not meaningful for `p > c̄`. -/
theorem seller_service_choice (M : Model) :
    (0 < M.sellerPayoff M.cbar M.f ∧
      ∀ p ∈ Set.Ioc 0 M.cbar, 0 < M.sellerPayoff p M.f) ∧
    M.sellerPayoff M.cbar M.f < M.sellerPayoff M.cown M.F ∧
    (StrictAntiOn (fun p => M.sellerPayoff p M.f) (Set.Ioc 0 M.cbar) ∧
      ∀ p ∈ Set.Ioc 0 M.cbar, M.sellerPayoff M.cbar M.f ≤ M.sellerPayoff p M.f) ∧
    ∀ p, M.cbar < p → ∀ x ∈ M.J, M.sellerProfit p M.f x < M.sellerPayoff M.cbar M.f := by sorry

end MarketplaceScalability
