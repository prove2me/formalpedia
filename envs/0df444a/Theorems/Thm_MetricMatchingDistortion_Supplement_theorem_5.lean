-- Prove2me | Theorems.Thm_MetricMatchingDistortion_Supplement_theorem_5
-- name    : MetricMatchingDistortion.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:03:59.453496+00:00
-- url     : https://prove2.me/theorems/d91ac2ef-e1ce-459d-9ca1-db94a909baf0
-- title:
--   Theorem 5 — Coordinated Merging: distortion at most $2n^{\alpha_\star}-1$
-- statement:
--   Let $\alpha_\star\approx0.95084$ be the unique solution in $(0,1)$ of equation (12). There is a randomized ordinal matching mechanism $\mathcal A$ such that for every $n\ge1$, every instance $\sigma$ with $n$ agents, every pseudometric $d$ consistent with $\sigma$ and every perfect matching $\pi^*$,
--   $$\mathbb E_{M\sim\mathcal A(\sigma)}[\mathrm{cost}(M,d)]\le\big(2n^{\alpha_\star}-1\big)\,\mathrm{cost}(\pi^*,d).$$
--   In particular $\mathrm{distortion}(\mathcal A,\sigma)\le 2n^{\alpha_\star}-1$. The statement also asserts that equation (12) has exactly one solution in $(0,1)$.
--
--   This is the sharpest explicit upper bound the paper proves with a single algorithm before the $O(n^{\log_4 3})$ bound of the goal.
--
--   Differences from the source:
--   - reading: α ≈ 0.95084, the α⋆ of Definition 4.6 ('the unique solution in (0, 1)' of (12)) → ∃ α with IsAlphaStar α, every solution of (12) in (0,1) equals α, and the bound holds with exponent α; reason: Definition 4.6 presupposes existence and uniqueness (proved in Appendix B); stating them ties the bound to the root and never to a decimal
--   - encoding: distortion(M, σ) ≤ B (supremum of E[cost]/min cost, footnote 10) → E[cost] ≤ B · cost(π*, d) for every consistent d and every perfect matching π*; reason: for OPT > 0 take π* optimal; for OPT = 0 the page's c/0 = +∞ forces E[cost] = 0 and 0/0 = 1 ≤ B; same convention as the published HasDistortionO
--   - encoding: an algorithm A (Algorithm 6) → ∃ A : Mechanism (a map from rankings to a PMF over perfect matchings); reason: the theorem is existential; a mechanism is ordinal by its type
--   - encoding: any instance σ → every n ≥ 1 and every ranking profile on Fin n; reason: the standing assumption n ≥ 1 of §2
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 5, p.18 (PDF p.20); Definition 4.6, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_Mechanism
import Definitions.Def_MetricMatchingDistortion_Supplement_IsAlphaStar

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- **Theorem 5 (Coordinated Merging).** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Theorem 5, p.18 (PDF p.20): "There
exists an algorithm A such that for any ordinal preference instance σ, distortion(A, σ) ≤ 2n^α − 1
where α ≈ 0.95084." The exponent is `α⋆` of Definition 4.6, p.27 ("Initially k = n, so (14) gives
distortion at most 2n^{α⋆} − 1").

The root `α⋆ ∈ (0, 1)` of (12) exists and is unique, and there is a mechanism `A`, seeing only the
rankings, such that for every `n ≥ 1`, every ranking profile `rk`, every consistent pseudometric `d`
and every perfect matching `π*`,
`E_{M∼A(rk)}[cost(M, d)] ≤ (2 n^{α⋆} − 1) · cost(π*, d)`.

**Formalization Note.** The distortion bound is the inequality against every perfect matching, as
in the base mission's `HasDistortionO`: with the page's `c/0 = +∞` an optimum of `0` forces expected
cost `0`, and `0/0 = 1 ≤ 2n^{α⋆} − 1`. `α⋆` is "the unique solution in (0, 1)" of (12); its
existence and uniqueness (Appendix B) are stated as conjuncts, so the bound is about that root and
never about the decimal `0.95084`. -/
theorem theorem_5 :
    ∃ α : ℝ, IsAlphaStar α ∧ (∀ β : ℝ, IsAlphaStar β → β = α) ∧
      ∃ A : Mechanism, ∀ n : ℕ, 1 ≤ n → ∀ rk : Ranking n,
        ∀ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d →
          ∀ πstar : Equiv.Perm (Fin n),
            expectedCost A n rk d ≤ (2 * (n : ℝ) ^ α - 1) * matchingCost πstar d := by sorry

end MetricMatchingDistortion.Supplement
