-- Prove2me | Theorems.Thm_MarketplaceScalability_hasDerivAt_pi
-- name    : MarketplaceScalability.hasDerivAt_pi
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:26.784357+00:00
-- url     : https://prove2.me/theorems/e345babc-eea3-40f9-836f-bbfeede29a73
-- title:
--   Proof of Lemma 2 — the derivative of $\pi$ (corrected: demand conditions)
-- statement:
--   For every $p\in(0,\bar c]$,
--   $$
--   \pi'(p)=q(p)+\Big(\frac{p}{1-\alpha}-c\Big)q'(p).
--   $$
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - encoding: π′(p) for all prices p → p ∈ (0, c̄]; reason: under the corrected conditions the first-order condition is guaranteed solvable only on (0, c̄], and the proof of Proposition 1 uses no other prices
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, proof of Lemma 2, p.25

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_pi

namespace MarketplaceScalability

/-- **π′, proof of Lemma 2, p.25.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "The first order derivative of π(p) is
π′(p) = q(p) + (p/(1 − α) − c)q′(p)." -/
theorem hasDerivAt_pi (M : Model) {p : ℝ} (hp : p ∈ Set.Ioc 0 M.cbar) :
    HasDerivAt M.pi (M.q p + (p / (1 - M.α) - M.c) * deriv M.q p) p := by sorry

end MarketplaceScalability
