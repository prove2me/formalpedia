-- Prove2me | Theorems.Thm_MarketplaceScalability_hasDerivAt_q
-- name    : MarketplaceScalability.hasDerivAt_q
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:46.726184+00:00
-- url     : https://prove2.me/theorems/04a88157-c028-43b9-b0b5-2793b1b3852c
-- title:
--   Proof of Lemma 2 — $q'(p)=1/((1-\alpha)D'(q(p)))<0$ (corrected: demand conditions)
-- statement:
--   For every $p\in(0,\bar c]$, $q$ is differentiable at $p$ with
--   $$
--   q'(p)=\frac{1}{(1-\alpha)D'(q(p))}<0.
--   $$
--
--   **Formalization Note** The derivative is two-sided at $p=\bar c$: $D$ is continuous and strictly decreasing around the interior point $q_m$, so $q$ inverts $(1-\alpha)D$ on a neighbourhood of $\bar c$.
--
--   Differences from the source:
--   - correction: D > 0, D′ < 0, D″ ≤ 0, D(0) = ∞ on outputs q ≥ 0 (p.4) → outputs in J = (0, q̄), the signs on J, and (1 − α)D(q) = p solvable in J for every p ∈ (0, c̄]; reason: the printed conditions are unsatisfiable: a positive concave function on (0, ∞) cannot be strictly decreasing, and a concave function on (0, b) cannot tend to +∞ at 0; solvability of the first-order condition is the only use of D(0) = ∞
--   - generalization: α a commission rate, Assumption 2 → 0 ≤ α < 1, and of Assumption 2 only f < F; reason: the argument uses no more, and low-type sellers are absent at μ = 1; every source instance, with α ∈ (0, 1), is covered
--   - encoding: c ∈ (c̲, c̄) with no sign on c̲ (p.6) → 0 < c̲; reason: (1 − α)D(q(c̲)) = c̲ with D > 0 and α < 1 forces c̲ > 0, so no source instance is excluded
--   - encoding: q′(p) for all prices p → p ∈ (0, c̄]; reason: under the corrected conditions the first-order condition is guaranteed solvable only on (0, c̄], and the proof of Proposition 1 uses no other prices
-- source:
--   Li, Pisano, Xu & Zhu, Marketplace Scalability and Strategic Use of Platform Investment, SSRN 3310484, proof of Lemma 2, p.25

import Mathlib
import Definitions.Def_MarketplaceScalability_Model

namespace MarketplaceScalability

/-- **q′, proof of Lemma 2, p.25.** Li, Pisano, Xu & Zhu, *Marketplace Scalability and Strategic Use of Platform Investment*, SSRN 3310484: "note first that by implicit function theorem
q′(p) = 1 / ((1 − α)D′(q(p))) < 0."

For `p ∈ (0, c̄]` the derivative exists, two-sided, and has this value.

**Formalization Note** At `p = c̄` the two-sided derivative makes sense because `D` is continuous and
strictly decreasing near the interior point `q_m`, so `q` is the inverse of `(1 − α) D` on a neighbourhood
of `c̄`. -/
theorem hasDerivAt_q (M : Model) {p : ℝ} (hp : p ∈ Set.Ioc 0 M.cbar) :
    HasDerivAt M.q (1 / ((1 - M.α) * deriv M.D (M.q p))) p ∧
    1 / ((1 - M.α) * deriv M.D (M.q p)) < 0 := by sorry

end MarketplaceScalability
