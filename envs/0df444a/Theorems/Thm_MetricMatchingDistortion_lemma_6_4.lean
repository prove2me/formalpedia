-- Prove2me | Theorems.Thm_MetricMatchingDistortion_lemma_6_4
-- name    : MetricMatchingDistortion.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:20:51.043456+00:00
-- url     : https://prove2.me/theorems/40a75c8b-9211-4a54-bb0d-4ff77327548e
-- title:
--   Lemma 6.4 — rate inequality $\partial_t\,\mathrm{cost}(X(t),d)=\sum_a d(a,b_a(t))\le\frac{\mathrm{cost}(M^*,d)+\mathrm{cost}(X(t),d)}{1-t}$
-- statement:
--   For every $n\ge1$, every ranking profile, every pseudometric $d$ consistent with it, every perfect matching $\pi^*$ and every $t\in[0,1)$:
--   $$\partial_t\,\mathrm{cost}(X(t),d)=\sum_a d(a,b_a(t))\le\frac{\mathrm{cost}(\pi^*,d)+\mathrm{cost}(X(t),d)}{1-t},$$
--   where $\partial_t$ is the right derivative in $t$ and $b_a(t)$ is the item agent $a$ eats just after time $t$.
--
--   Integrating this rate gives the prefix bound of Corollary 6.6.
--
--   Differences from the source:
--   - encoding: ∂_t, the right derivative with respect to t → HasDerivWithinAt on [t, ∞); reason: the right derivative in Mathlib's form
--   - encoding: OPT = cost(M*, d) for an optimal matching M* → cost(π*, d) for every perfect matching π*; reason: OPT is the minimum over perfect matchings and the coefficient is nonnegative, so the two bounds are equivalent
--   - encoding: X(t) = PS run for t units of time (Algorithm 7) → psAlloc: the eating step ExAnteExPost.RPS.eatStep with favorite-available-item picks, iterated n+1 times from capacities 1, the zero matrix and time budget t; reason: every step but the last exhausts an item, so n+1 steps run PS to time t
--   - encoding: n ≥ 1 (standing, §2 p.9) → [NeZero n]; reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Lemma 6.4, p.52 (PDF p.54)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_IsPartialFractionalMatching
import Definitions.Def_MetricMatchingDistortion_psAlloc

namespace MetricMatchingDistortion

/-- **Lemma 6.4 (Rate inequality).** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), Lemma 6.4, p.52 (PDF p.54): "At every time t ∈ [0, 1), ∂_t cost(X(t), d) = ∑_a d(a, b_a(t)) ≤
(cost(M∗, d) + cost(X(t), d)) / (1 − t)." p.52: "we let ∂_t denote the right derivative with respect
to t".

For `t ∈ [0, 1)`, every consistent pseudometric `d` and every perfect matching `π*`: the map
`s ↦ cost(X(s), d)` has right derivative `∑_a d(a, b_a(t))` at `t`, and this rate is at most
`(cost(π*, d) + cost(X(t), d)) / (1 − t)`.

**Formalization Note.** The right derivative is `HasDerivWithinAt` on `[t, ∞)`. `M∗` may be any
perfect matching. -/
theorem lemma_6_4 (n : ℕ) [NeZero n] (rk : Ranking n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ)
    (hd : IsConsistentPseudometric rk d) (πstar : Equiv.Perm (Fin n)) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    HasDerivWithinAt (fun s => fracCost (psAlloc rk s) d)
        (∑ a, d (Sum.inl a) (Sum.inr (eatenItem rk t a))) (Set.Ici t) t ∧
      ∑ a, d (Sum.inl a) (Sum.inr (eatenItem rk t a)) ≤
        (matchingCost πstar d + fracCost (psAlloc rk t) d) / (1 - t) := by sorry

end MetricMatchingDistortion
