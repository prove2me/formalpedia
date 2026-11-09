-- Prove2me | Theorems.Thm_MetricMatchingDistortion_corollary_6_6
-- name    : MetricMatchingDistortion.corollary_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:20:44.592545+00:00
-- url     : https://prove2.me/theorems/3a03c844-5099-4a62-bfc5-921599a1e210
-- title:
--   Corollary 6.6 — $\mathrm{cost}(X(t),d)\le\frac{t}{1-t}\mathrm{cost}(M^*,d)$ and $\sum_a d(a,b_a(t))\le\frac{\mathrm{cost}(M^*,d)}{(1-t)^2}$
-- statement:
--   For every $n\ge1$, every ranking profile, every pseudometric $d$ consistent with it, every perfect matching $\pi^*$ and every $t\in[0,1)$:
--   $$\mathrm{cost}(X(t),d)\le\frac{t}{1-t}\,\mathrm{cost}(\pi^*,d)\qquad\text{and}\qquad\sum_a d(a,b_a(t))\le\frac{\mathrm{cost}(\pi^*,d)}{(1-t)^2}.$$
--
--   At $t=1-k/n$ the first inequality bounds the PS prefix by $\frac{n-k}{k}\,\mathrm{OPT}$, the prefix term of Equation (5).
--
--   Differences from the source:
--   - encoding: OPT = cost(M*, d) for an optimal matching M* → cost(π*, d) for every perfect matching π*; reason: OPT is the minimum over perfect matchings and the coefficient is nonnegative, so the two bounds are equivalent
--   - encoding: X(t) = PS run for t units of time (Algorithm 7) → psAlloc: the eating step ExAnteExPost.RPS.eatStep with favorite-available-item picks, iterated n+1 times from capacities 1, the zero matrix and time budget t; reason: every step but the last exhausts an item, so n+1 steps run PS to time t
--   - encoding: n ≥ 1 (standing, §2 p.9) → [NeZero n]; reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Corollary 6.6, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_psAlloc

namespace MetricMatchingDistortion

/-- **Corollary 6.6.** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), Corollary 6.6, p.53 (PDF p.55): "For every t ∈ [0, 1), cost(X(t), d) ≤ (t / (1 − t)) cost(M∗, d) and
∑_a d(a, b_a(t)) ≤ cost(M∗, d) / (1 − t)²."

Both inequalities, for every `t ∈ [0, 1)`, every consistent pseudometric `d` and every perfect
matching `π*`.

**Formalization Note.** `M∗` may be any perfect matching. -/
theorem corollary_6_6 (n : ℕ) [NeZero n] (rk : Ranking n)
    (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) (hd : IsConsistentPseudometric rk d)
    (πstar : Equiv.Perm (Fin n)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    fracCost (psAlloc rk t) d ≤ t / (1 - t) * matchingCost πstar d ∧
      ∑ a, d (Sum.inl a) (Sum.inr (eatenItem rk t a)) ≤ matchingCost πstar d / (1 - t) ^ 2 := by sorry

end MetricMatchingDistortion
