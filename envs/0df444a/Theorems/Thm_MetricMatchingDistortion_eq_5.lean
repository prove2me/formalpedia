-- Prove2me | Theorems.Thm_MetricMatchingDistortion_eq_5
-- name    : MetricMatchingDistortion.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:17.362445+00:00
-- url     : https://prove2.me/theorems/7f307521-a325-4476-a9ff-cd4e0d454304
-- title:
--   Equation (5) — $\mathbb E[\mathrm{cost}(M,d)]\le\left(\frac{n-k}{k}+2kn^\theta\right)\mathrm{OPT}$ for the completed PS prefix
-- statement:
--   Let $\theta=\log_2(3/2)$. For every $n\ge1$, every ranking profile, every selection rule as in Algorithm 2, every completion map with the guarantee of Lemma 3.1, every real $0<k\le n$, every pseudometric $d$ consistent with the rankings and every perfect matching $\pi^*$: drawing $\mathcal P$ from RandRepPartition and completing the PS prefix, $M=\mathrm{complete}(X(1-k/n),\mathcal P)$,
--   $$\mathbb E[\mathrm{cost}(M,d)]\le\left(\frac{n-k}{k}+2kn^\theta\right)\mathrm{cost}(\pi^*,d).$$
--
--   Choosing $k=n^{(1-\theta)/2}$ gives $3n^{\log_4 3}\,\mathrm{OPT}$, the bound behind Theorem 4.
--
--   Differences from the source:
--   - generalization: M = ClusterCompletion(X(1 − k/n), P) (Algorithm 1) → M = complete(X(1 − k/n), P) for every map complete with the guarantee of Lemma 3.1; reason: by Lemma 3.1 Algorithm 1 (with any fixed path choice) is such a map
--   - reading: Choose such clusters S, T by a fixed rule → a rule is a function of the current clusters and representatives (and of σ); reason: the state of Algorithm 2 is its clusters and representatives
--   - generalization: one fixed rule → every selection rule that proposes an admissible merge (overlapping, p = |S| ≥ q = |T|) whenever two claimed prefixes overlap; reason: any fixed rule is such a rule, so the statement specializes to the page's
--   - encoding: OPT = cost(M*, d) for an optimal matching M* → cost(π*, d) for every perfect matching π*; reason: OPT is the minimum over perfect matchings and the coefficient is nonnegative, so the two bounds are equivalent
--   - encoding: E over P ← RandRepPartition(σ) → finite sum over labellings weighted by the output law; reason: the law of a finite random object
--   - encoding: X(t) = PS run for t units of time (Algorithm 7) → psAlloc: the eating step ExAnteExPost.RPS.eatStep with favorite-available-item picks, iterated n+1 times from capacities 1, the zero matrix and time budget t; reason: every step but the last exhausts an item, so n+1 steps run PS to time t
--   - encoding: n ≥ 1 (standing, §2 p.9) → [NeZero n]; reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §3.3, p.17 (PDF p.19), Equation (5)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_matchingCost
import Definitions.Def_MetricMatchingDistortion_IsClusterCompletion
import Definitions.Def_MetricMatchingDistortion_randRepPartition
import Definitions.Def_MetricMatchingDistortion_psAlloc

namespace MetricMatchingDistortion

/-- **Equation (5): the completed PS prefix.** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), §3.3, p.17 (PDF p.19): "Complete this prefix using M = ClusterCompletion(X(1 − k/n), P). By Lemmas
3.1 and 3.2, the resulting perfect fractional matching satisfies E[cost(M, d)] ≤ ((n − k)/k +
2kn^θ) OPT. (5)" Here P ← RandRepPartition(σ) (p.16), k is real with 0 < k ≤ n (p.17), and
θ = log₂(3/2).

For every selection rule as in Algorithm 2, every completion map with the guarantee of Lemma 3.1,
every real `0 < k ≤ n`, every consistent pseudometric `d` and every perfect matching `π*`:
the expected cost of `M = complete(X(1 − k/n), P)` over `P ∼ RandRepPartition` is at most
`((n − k)/k + 2 k n^θ) cost(π*, d)`.

**Formalization Note.** ClusterCompletion is any map with the guarantee of Lemma 3.1
(`IsClusterCompletion`), of which Algorithm 1 with any fixed path choice is one. `M∗` may be any
perfect matching. -/
theorem eq_5 (n : ℕ) [NeZero n] (rk : Ranking n) (rule : SelectionRule n)
    (hrule : IsSelectionRule rk rule)
    (complete : (Fin n → Fin n → ℝ) → (Fin n ⊕ Fin n → Fin n) → (Fin n → Fin n → ℝ))
    (hcomplete : IsClusterCompletion complete) (k : ℝ) (hk0 : 0 < k) (hkn : k ≤ n)
    (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) (hd : IsConsistentPseudometric rk d)
    (πstar : Equiv.Perm (Fin n)) :
    ∑ c, (randRepPartition rk rule c).toReal * fracCost (complete (psAlloc rk (1 - k / n)) c) d ≤
      ((n - k) / k + 2 * k * (n : ℝ) ^ theta) * matchingCost πstar d := by sorry

end MetricMatchingDistortion
