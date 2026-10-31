-- Prove2me | Theorems.Thm_MarketplaceScalability_margins_rewritten
-- name    : MarketplaceScalability.margins_rewritten
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:53:40.184921+00:00
-- url     : https://prove2.me/theorems/ea78e376-dc6e-43ba-a313-9ca7ef13e6ee
-- title:
--   Proof of Proposition 1 — the margins rewritten, with attained maxima (corrected: demand conditions)
-- statement:
--   Let $p_s$ be the cutoff price. Then $\pi$ attains its maximum on $(0,\bar c]$ and on $(0,p_s]$, each of these maximizers is unique, and
--   $$
--   I_N=\max\Big\{\max_{p\le\bar c}\pi(p)-\pi_m,\,0\Big\},\qquad
--   I_S=\max\Big\{\max_{p\le p_s}\pi(p)-\pi_o,\,0\Big\}.
--   $$
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - generalization: the displayed rewriting, with max taken for granted → also attainment and uniqueness on the half-open sets; reason: the page's max presupposes attainment; uniqueness is what "the" optimal price needs
--   - encoding: max over p ≤ c̄ and p ≤ p_s → sSup over prices in (0, c̄] and (0, p_s]; reason: the sSup are the maxima, by the attainment clauses; prices are positive
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, proof of Proposition 1, p.25

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_piM
import Definitions.Def_MarketplaceScalability_Params_piO
import Definitions.Def_MarketplaceScalability_Params_IN
import Definitions.Def_MarketplaceScalability_Params_IS

namespace MarketplaceScalability

/-- **The margins rewritten, proof of Proposition 1, p.25.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "Rewrite the profit margins as
I_N = max{max_{p≤c̄} π(p), π_m} − π_m = max{max_{p≤c̄} π(p) − π_m, 0},
I_S = max{max_{p≤p_s} π(p), π_o} − π_o = max{max_{p≤p_s} π(p) − π_o, 0}".

With `p_s` the cutoff price, `π` attains its maximum on `(0, c̄]` and on `(0, p_s]`, each maximizer is
unique, and both margins have the displayed form.

**Formalization Note** Attainment on the half-open sets is part of the statement: the page's `max`
presupposes it. The `sSup` below are these maxima. -/
theorem margins_rewritten (M : Model) {ps : ℝ} (hps : ps ∈ Set.Ioc 0 M.cbar)
    (hcut : M.sellerPayoff ps M.f = M.sellerPayoff M.cown M.F) :
    (∃ p ∈ Set.Ioc 0 M.cbar, IsMaxOn M.pi (Set.Ioc 0 M.cbar) p) ∧
    (∃ p ∈ Set.Ioc 0 ps, IsMaxOn M.pi (Set.Ioc 0 ps) p) ∧
    (∀ p ∈ Set.Ioc 0 M.cbar, ∀ p' ∈ Set.Ioc 0 M.cbar,
      IsMaxOn M.pi (Set.Ioc 0 M.cbar) p → IsMaxOn M.pi (Set.Ioc 0 M.cbar) p' → p = p') ∧
    (∀ p ∈ Set.Ioc 0 ps, ∀ p' ∈ Set.Ioc 0 ps,
      IsMaxOn M.pi (Set.Ioc 0 ps) p → IsMaxOn M.pi (Set.Ioc 0 ps) p' → p = p') ∧
    M.IN = max (sSup (M.pi '' Set.Ioc 0 M.cbar) - M.piM) 0 ∧
    M.IS = max (sSup (M.pi '' Set.Ioc 0 ps) - M.piO) 0 := by sorry

end MarketplaceScalability
