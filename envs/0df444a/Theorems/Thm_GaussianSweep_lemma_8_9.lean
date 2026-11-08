-- Prove2me | Theorems.Thm_GaussianSweep_lemma_8_9
-- name    : GaussianSweep.lemma_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:47.367538+00:00
-- url     : https://prove2.me/theorems/e437997d-ade5-46e2-8e7a-460a9fa1251b
-- title:
--   Lemma 8.9 — switch lemma: contribution to $L_0$ at most $\kappa(r)$
-- statement:
--   Let $r \in (0,1)$, let $0 \le d \le 3$, and let $(Y_0, Y_1, \dots, Y_d)$ be a centered Gaussian vector with unit variances and $\mathrm{Corr}(Y_0, Y_i) \ge r$ for $1 \le i \le d$. Then
--   $$
--   \mathbb P\big(Y_0 \le 0,\ \exists i : Y_i > 0\big) + \mathbf 1_{d=3}\,\mathbb P\big(Y_0 > 0,\ Y_i \le 0 \text{ for all } i\big) \le \kappa(r).
--   $$
--   Applied to a vertex of degree $d$ and its neighbors, the two events are $v \in U$ and $v \in D \cap W$, so each vertex contributes in expectation at most $\kappa(r)$ to $L_0$; by sign symmetry the same holds for $L_0'$.
--
--   **Formalization Note** The vector is given through its law $N(0, S)$, quantified over all correlation matrices $S$ of size $d+1$; coordinate $0$ is $Y_0$ and the indices $i$ range over $1, \dots, d$. The indicator $\mathbf 1_{d=3}$ is a case distinction: for $d < 3$ the second term is absent.
--
--   Differences from the source:
--   - encoding: a centered Gaussian vector (Y₀, …, Y_d) with unit variances → its law multivariateGaussian 0 S, quantified over every positive semidefinite S with unit diagonal (singular allowed); reason: the law of a centered Gaussian vector is N(0, S) for its covariance S, and the events depend only on the law
--   - encoding: 1_{d=3} · P(…) → if d = 3 then P(…) else 0; reason: the indicator of the condition d = 3
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.9, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_GaussianSweep_kappa
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- Lemma 8.9 (switch lemma) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.9, p.51 (PDF p.53)). Let `r ∈ (0, 1)`, `0 ≤ d ≤ 3`,
and `(Y₀, Y₁, …, Y_d)` a centered Gaussian vector with unit variances and `Corr(Y₀, Yᵢ) ≥ r` for
`1 ≤ i ≤ d`. Then `P(Y₀ ≤ 0, ∃ i : Yᵢ > 0) + 1_{d=3} P(Y₀ > 0, Yᵢ ≤ 0 for all i) ≤ κ(r)`.

**Formalization Note** A centered Gaussian vector `(Y₀, …, Y_d)` with unit variances has law
`N(0, S)` with `S` its correlation matrix (positive semidefinite, unit diagonal, possibly
singular); the statement quantifies over all such `S` and is about `multivariateGaussian 0 S` on
`EuclideanSpace ℝ (Fin (d + 1))`. Coordinate `0` is the center `Y₀` and `Corr(Y₀, Yᵢ) = S 0 i`. The indicator `1_{d=3}` is an `if`: for `d < 3` the second term is absent. -/
theorem lemma_8_9 (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (d : ℕ) (hd : d ≤ 3)
    (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hS : S.PosSemidef) (hdiag : ∀ i, S i i = 1)
    (hcorr : ∀ i, i ≠ 0 → r ≤ S 0 i) :
    (multivariateGaussian 0 S).real {Y | Y 0 ≤ 0 ∧ ∃ i, i ≠ 0 ∧ 0 < Y i} +
        (if d = 3 then (multivariateGaussian 0 S).real {Y | 0 < Y 0 ∧ ∀ i, i ≠ 0 → Y i ≤ 0}
          else 0) ≤ kappa r := by sorry

end GaussianSweep
