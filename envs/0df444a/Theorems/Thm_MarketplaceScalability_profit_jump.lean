-- Prove2me | Theorems.Thm_MarketplaceScalability_profit_jump
-- name    : MarketplaceScalability.profit_jump
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:37.080378+00:00
-- url     : https://prove2.me/theorems/df65a586-b8ef-40ee-a8cf-50fa33997d54
-- title:
--   §3.1 — the profit jump at $p=\bar c$ (corrected: demand conditions)
-- statement:
--   At the market price the platform's profit jumps by a positive amount:
--   $$
--   \pi(\bar c)-\pi_m=(\bar c-c)\,q_m>0.
--   $$
--   Hence $\pi_m<\sup_{p>0}\pi_N(p)$, and every maximizer of $\pi_N$ over prices $p>0$ lies in $(0,\bar c]$.
--
--   So, in the non-scalable scenario, an optimal price always attracts the sellers.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - reading: its profit jumps → the size of the jump, its sign, and the consequence for maximizers of π_N; reason: the source's claim made quantitative; the last clause is what p.8 uses when it reads p* against c̄
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, §3.1, p.8

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_piN
import Definitions.Def_MarketplaceScalability_Params_qm

namespace MarketplaceScalability

/-- **The jump at c̄, p.8.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484, §3.1, p.8: "as the platform lowers its price to p = c̄, its profit
jumps because the sellers switch from the market service to the platform service, allowing the
platform to make profits from its own ancillary service."

The jump is `π(c̄) − π_m = (c̄ − c) q_m > 0`. Hence `π_m` is below the supremum of `π_N`, and every maximizer
of `π_N` over prices `p > 0` lies in `(0, c̄]`. -/
theorem profit_jump (M : Model) :
    M.pi M.cbar - M.piM = (M.cbar - M.c) * M.qm ∧
    0 < (M.cbar - M.c) * M.qm ∧
    M.piM < sSup (M.piN '' Set.Ioi 0) ∧
    ∀ p ∈ Set.Ioi 0, IsMaxOn M.piN (Set.Ioi 0) p → p ∈ Set.Ioc 0 M.cbar := by sorry

end MarketplaceScalability
