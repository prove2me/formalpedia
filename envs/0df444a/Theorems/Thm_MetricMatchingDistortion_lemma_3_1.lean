-- Prove2me | Theorems.Thm_MetricMatchingDistortion_lemma_3_1
-- name    : MetricMatchingDistortion.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:52.389953+00:00
-- url     : https://prove2.me/theorems/b9cd60d4-1972-49a7-99e8-2e0bec6f63f8
-- title:
--   Lemma 3.1 — completion from a balanced partition
-- statement:
--   For every $n\ge1$ there is a completion map that sees only a partial fractional matching $X$ and a partition $\mathcal P$ such that, for every partial fractional matching $X$ with unmatched mass $k=n-\sum_{a,b}X_{a,b}$ and every balanced partition $\mathcal P=(A_j,B_j)_j$, the output $M$ is a perfect fractional matching and for every distance $d\ge0$ on agent–item pairs
--   $$\mathrm{cost}(M,d)\le\mathrm{cost}(X,d)+\sum_j\min\{k,|A_j|\}\,w_j\le\mathrm{cost}(X,d)+k\,W(\mathcal P,d).\qquad(3)$$
--
--   A partition with small cost $W$ thus lets any partial matching be completed at extra cost $k\,W$, where $k$ is the mass still to be assigned.
--
--   Differences from the source:
--   - reading: Algorithm 1 uses only X and the cluster memberships to return a perfect fractional matching M → there is a map complete X c (a function of X and the labelling only) whose output has the guarantee; reason: Algorithm 1 chooses its augmenting paths freely, so it is not a function; each fixed path choice is such a map
--   - generalization: for every d ∈ ρ(σ) → for every d nonnegative on agent–item pairs; reason: the bound uses only d ≥ 0; ρ(σ) is contained in this class
--   - encoding: balanced partition P = (A_j, B_j)_{j=1}^m → labelling c : Fin n ⊕ Fin n → Fin n with as many agents as items per label; reason: the same partitions; unused labels have no agent, no item and w_j = 0
--   - encoding: w_j = max over a ∈ A_j, b ∈ B_j of d(a,b) → maximum of 0 and these distances; reason: equal for nonnegative d on a nonempty cluster; 0 for an unused label
--   - encoding: n ≥ 1 (standing, §2 p.9) → [NeZero n]; reason: the same condition as a type class
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Lemma 3.1, p.13 (PDF p.15), Equation (3)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_IsClusterCompletion

namespace MetricMatchingDistortion

/-- **Lemma 3.1 (Completion from a Balanced Partition).** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), Lemma 3.1, p.13 (PDF p.15): "Given a partial fractional matching X with unmatched mass k and a
balanced partition P, Algorithm 1 uses only X and the cluster memberships to return a perfect
fractional matching M satisfying cost(M, d) ≤ cost(X, d) + ∑_j min{k, |Aj|} wj ≤ cost(X, d) +
kW(P, d) (3) for every d ∈ ρ(σ)."

There is a completion map, a function of the partial matching and the labelling only, satisfying
both inequalities of (3) for every partial fractional matching, every balanced labelling and every
`d` nonnegative on agent–item pairs (see `IsClusterCompletion`).

**Formalization Note.** Algorithm 1 chooses its augmenting paths freely; the lemma asserts the
existence of a completion map with the guarantee (any fixed path choice of Algorithm 1 gives one).
The guarantee is required for every `d ≥ 0` on agent–item pairs, a class containing `ρ(σ)`. -/
theorem lemma_3_1 (n : ℕ) [NeZero n] :
    ∃ complete : (Fin n → Fin n → ℝ) → (Fin n ⊕ Fin n → Fin n) → (Fin n → Fin n → ℝ),
      IsClusterCompletion complete := by sorry

end MetricMatchingDistortion
