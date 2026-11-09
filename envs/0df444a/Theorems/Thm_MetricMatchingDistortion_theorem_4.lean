-- Prove2me | Theorems.Thm_MetricMatchingDistortion_theorem_4
-- name    : MetricMatchingDistortion.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:46.767443+00:00
-- url     : https://prove2.me/theorems/27a488d3-9562-4d67-866e-a745e25e5d36
-- title:
--   Theorem 4 — a randomized matching mechanism with metric distortion $O(n^{\log_4 3})$
-- statement:
--   There is a randomized matching mechanism $\mathcal A$, which sees only the agents' rankings, and a constant $C$ such that for every $n\ge1$, every instance $\sigma$ with $n$ agents and $n$ items, every pseudometric $d$ consistent with $\sigma$ and every perfect matching $\pi^*$,
--   $$\mathbb E_{M\sim\mathcal A(\sigma)}[\mathrm{cost}(M,d)]\le C\,n^{\log_4 3}\,\mathrm{cost}(\pi^*,d).$$
--   That is, $\mathrm{distortion}(\mathcal A,\sigma)=O(n^{\log_4 3})$ with $\log_4 3\approx 0.7925$: the first sublinear metric distortion bound for matching.
--
--   Differences from the source:
--   - encoding: distortion(A, σ) = sup over d ∈ ρ(σ) of E cost / min cost, with 0/0 = 1 and c/0 = +∞ → E cost ≤ C · n^{log_4 3} · cost(π*, d) for every perfect matching π*; reason: the same bound: a zero optimum forces zero expected cost, and 0/0 = 1 ≤ C · n^{log_4 3} once C ≥ 1
--   - reading: distortion(A, σ) = O(n^{log_4 3}) → one constant C for every n ≥ 1; reason: the stronger of the two readings of O(·) (all n rather than all large n); the paper's proof gives 3 n^{log_4 3} for every n ≥ 1
--   - encoding: instance σ = (A, B, {≻_a}) with |A| = |B| = n; mechanism = distribution over perfect integral matchings using the rankings → Ranking n on Fin n; Mechanism := ∀ n, Ranking n → PMF (Equiv.Perm (Fin n)); reason: every instance is a relabelling of one of these; the type keeps the metric out of the mechanism's input
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), Theorem 4, p.12 (PDF p.14); also p.4 (PDF p.6)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_HasDistortionO

namespace MetricMatchingDistortion

/-- **Theorem 4.** Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777 (held version,
sha256 fdf3452b…), Theorem 4, p.12 (PDF p.14): "There is a randomized matching mechanism A such that, for every instance σ with n agents,
distortion(A, σ) = O(n^{log_4 3})." (Also p.4: "There exists a randomized mechanism with distortion
O(n^{log_4 3}), where log_4 3 ≈ 0.7925.")

There is a mechanism `A`, seeing only the rankings, and a constant `C` such that for every
`n ≥ 1`, every ranking profile on `n` agents and `n` items, every consistent pseudometric `d`
and every perfect matching `π*`, `E_{M∼A(σ)}[cost(M, d)] ≤ C · n^{log_4 3} · cost(π*, d)`.

**Formalization Note.** Distortion `O(f(n))` is `HasDistortionO`: one `C` for all `n ≥ 1`,
instances and metrics, the ratio written as an inequality against every perfect matching (with
the page's `c/0 = +∞`, an optimum of `0` forces expected cost `0`). -/
theorem theorem_4 : ∃ A : Mechanism, HasDistortionO A fun n => (n : ℝ) ^ Real.logb 4 3 := by sorry

end MetricMatchingDistortion
