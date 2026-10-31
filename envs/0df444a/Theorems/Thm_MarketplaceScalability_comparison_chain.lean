-- Prove2me | Theorems.Thm_MarketplaceScalability_comparison_chain
-- name    : MarketplaceScalability.comparison_chain
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:52:01.454882+00:00
-- url     : https://prove2.me/theorems/bbd68eec-ff91-4c2f-aaa8-9c1c92ab4462
-- title:
--   Proof of Proposition 1 — the comparison chain for (a) (corrected: demand conditions)
-- statement:
--   Let $p_s$ be the cutoff price. Then
--   $$
--   \max_{p\le p_s}\pi(p)-\pi_o\le\max_{p\le\bar c}\pi(p)-\pi_m,
--   $$
--   and
--   $$
--   \max_{p\le p_s}\pi(p)-\max_{p\le\bar c}\pi(p)\le0\le\pi_o-\pi_m.
--   $$
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - reading: π0 − πm in the display on p.26 → π_o − π_m; reason: a printed slip for π_o
--   - encoding: max over p ≤ c̄ and p ≤ p_s → sSup over prices in (0, c̄] and (0, p_s]; reason: the sSup are the maxima, by the theorem rewriting the margins; prices are positive
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, proof of Proposition 1, pp.25–26

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_piM
import Definitions.Def_MarketplaceScalability_Params_piO
import Definitions.Def_MarketplaceScalability_Params_pi

namespace MarketplaceScalability

/-- **The chain for (a), proof of Proposition 1, pp.25–26.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: the sufficient condition
`max_{p≤c̄} π(p) − π_m ≥ max_{p≤p_s} π(p) − π_o` (p.25), and "When the platform service is provided,
since p_s < c̄, we have max_{p≤p_s} π(p) − max_{p≤c̄} π(p) ≤ 0 ≤ π_o − π_m" (p.26).

**Formalization Note** The page prints `π0` for `π_o` in the last display. -/
theorem comparison_chain (M : Model) {ps : ℝ} (hps : ps ∈ Set.Ioc 0 M.cbar)
    (hcut : M.sellerPayoff ps M.f = M.sellerPayoff M.cown M.F) :
    sSup (M.pi '' Set.Ioc 0 ps) - M.piO ≤ sSup (M.pi '' Set.Ioc 0 M.cbar) - M.piM ∧
    sSup (M.pi '' Set.Ioc 0 ps) - sSup (M.pi '' Set.Ioc 0 M.cbar) ≤ 0 ∧
    0 ≤ M.piO - M.piM := by sorry

end MarketplaceScalability
