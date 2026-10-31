-- Prove2me | Theorems.Thm_MarketplaceScalability_hasDerivAt_ratio
-- name    : MarketplaceScalability.hasDerivAt_ratio
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:40.260375+00:00
-- url     : https://prove2.me/theorems/eb3e1fc0-053d-4ff8-ad25-a5a0bd74d1ba
-- title:
--   Proof of Lemma 2 — the derivative of $\pi'/q'$ is positive (corrected: demand conditions)
-- statement:
--   For every $p\in(0,\bar c]$,
--   $$
--   \frac{d}{dp}\Big(\frac{\pi'(p)}{q'(p)}\Big)=1+\frac1{1-\alpha}+(1-\alpha)D''(q(p))\,q(p)\,q'(p)>0.
--   $$
--
--   Since $q'<0$, this says that $\pi'$ changes sign at most once, from positive to negative. This is where $D''\le0$ is used.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - encoding: d/dp(π′/q′) for all prices p → p ∈ (0, c̄]; reason: under the corrected conditions the first-order condition is guaranteed solvable only on (0, c̄], and the proof of Proposition 1 uses no other prices
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, proof of Lemma 2, p.25

import Mathlib
import Definitions.Def_MarketplaceScalability_Model
import Definitions.Def_MarketplaceScalability_Params_pi

namespace MarketplaceScalability

/-- **The second step, proof of Lemma 2, p.25.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "Divide both sides with q′(p), which is always
negative, and take derivative again d/dp(π′(p)/q′(p)) = 1 + 1/(1 − α) + (1 − α)D″(q(p))q(p)q′(p) > 0".

**Formalization Note** The formula of `hasDerivAt_pi` holds on a neighbourhood of every `p ∈ (0, c̄]`,
including `c̄`, because `D` is strictly decreasing around the interior point `q_m`. -/
theorem hasDerivAt_ratio (M : Model) {p : ℝ} (hp : p ∈ Set.Ioc 0 M.cbar) :
    HasDerivAt (fun r => deriv M.pi r / deriv M.q r)
      (1 + 1 / (1 - M.α) + (1 - M.α) * deriv (deriv M.D) (M.q p) * M.q p * deriv M.q p) p ∧
    0 < 1 + 1 / (1 - M.α) + (1 - M.α) * deriv (deriv M.D) (M.q p) * M.q p * deriv M.q p := by sorry

end MarketplaceScalability
