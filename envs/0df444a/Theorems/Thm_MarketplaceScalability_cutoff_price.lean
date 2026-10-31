-- Prove2me | Theorems.Thm_MarketplaceScalability_cutoff_price
-- name    : MarketplaceScalability.cutoff_price
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:04.679452+00:00
-- url     : https://prove2.me/theorems/2f1380f5-55cc-4ba6-b8a5-7e323444a3de
-- title:
--   §3.1 — the cutoff price $p_s$ exists and $p_s<\bar c$ (corrected: demand conditions)
-- statement:
--   There is exactly one $p_s\in(0,\bar c]$ with
--   $$
--   (1-\alpha)R(q(p_s))-p_s\,q(p_s)-f=(1-\alpha)R(q_o)-\underline c\,q_o-F.
--   $$
--   Moreover $\underline c<p_s<\bar c$, and for $p\in(0,\bar c]$ sellers weakly prefer the platform service to own service if and only if $p\le p_s$.
--
--   So the cutoff is lower than the market price: the sellers' outside option is better when they can scale.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - reading: the platform must charge a price less than p_s → p ≤ p_s; reason: indifferent sellers use the platform service, as (6) prints
--   - generalization: p_s < c̄ → also existence, uniqueness and c̲ < p_s; reason: the page assumes p_s exists; these are extra conclusions on top of the source's claim
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.9

import Mathlib
import Definitions.Def_MarketplaceScalability_Model

namespace MarketplaceScalability

/-- **The cutoff price, p.9.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §3.1, p.9: "Denote ps as the cutoff price satisfying
(1 − α)R(q(ps)) − psq(ps) − f = (1 − α)R(qo) − c̲qo − F. In other words, to attract sellers to use the
platform service, the platform must charge a price less than ps. Notice that ps < c̄".

There is exactly one `p_s ∈ (0, c̄]` with this equality. It satisfies `c̲ < p_s < c̄`, and a price
`p ∈ (0, c̄]` attracts sellers exactly when `p ≤ p_s`.

**Formalization Note** The page says "less than ps" where (6) has `p ≤ p_s`; indifferent sellers use
the platform service. `c̲ < p_s` is an addition: it gives existence, from `f < F`. -/
theorem cutoff_price (M : Model) :
    ∃ ps,
      (ps ∈ Set.Ioc 0 M.cbar ∧ M.sellerPayoff ps M.f = M.sellerPayoff M.cown M.F) ∧
      (∀ ps' ∈ Set.Ioc 0 M.cbar,
        M.sellerPayoff ps' M.f = M.sellerPayoff M.cown M.F → ps' = ps) ∧
      M.cown < ps ∧
      ps < M.cbar ∧
      ∀ p ∈ Set.Ioc 0 M.cbar,
        (M.sellerPayoff M.cown M.F ≤ M.sellerPayoff p M.f ↔ p ≤ ps) := by sorry

end MarketplaceScalability
