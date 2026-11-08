-- Prove2me | Theorems.Thm_GaussianSweep_proposition_8_8
-- name    : GaussianSweep.proposition_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:46.372609+00:00
-- url     : https://prove2.me/theorems/72ca1393-c98c-4b9b-80c7-4fcb63075bdf
-- title:
--   Proposition 8.8 — star bound at nonnegative thresholds: $\le f_{3,r}(t) \le \kappa(r)$
-- statement:
--   Let $r \in (0,1)$, let $0 \le d \le 3$, and let $(Y_0, Y_1, \dots, Y_d)$ be a centered Gaussian vector with unit variances and $\mathrm{Corr}(Y_0, Y_i) \ge r$ for $1 \le i \le d$. Then for every $t \ge 0$,
--   $$
--   \mathbb P\big(Y_0 \ge t,\ \exists i \in \{1, \dots, d\} : Y_i \le t\big) \le f_{3,r}(t) \le \kappa(r).
--   $$
--   No assumption is made on the correlations between $Y_i$ and $Y_j$ for $i, j \ge 1$, and the covariance matrix may be singular. Applied to a vertex and its neighbors, this bounds the probability that a vertex lies in an outer frontier at a positive threshold (and, by sign symmetry, in an inner frontier at a negative one).
--
--   **Formalization Note** The vector is given through its law $N(0, S)$, quantified over all correlation matrices $S$ of size $d+1$; coordinate $0$ is $Y_0$ and $\mathrm{Corr}(Y_0, Y_i) = S_{0i}$. The left event has the weak inequality $Y_0 \ge t$, as printed.
--
--   Differences from the source:
--   - encoding: a centered Gaussian vector (Y₀, …, Y_d) with unit variances → its law multivariateGaussian 0 S, quantified over every positive semidefinite S with unit diagonal (singular allowed); reason: the law of a centered Gaussian vector is N(0, S) for its covariance S, and the events depend only on the law
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Proposition 8.8, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_GaussianSweep_f3
import Definitions.Def_GaussianSweep_kappa
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- Proposition 8.8 (star bound at nonnegative thresholds) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Proposition 8.8, p.50
(PDF p.52)). Let `r ∈ (0, 1)`, `0 ≤ d ≤ 3`, and `(Y₀, Y₁, …, Y_d)` a centered Gaussian vector with
unit variances and `Corr(Y₀, Yᵢ) ≥ r` for `1 ≤ i ≤ d`. Then for every `t ≥ 0`,
`P(Y₀ ≥ t, ∃ i ∈ {1, …, d} : Yᵢ ≤ t) ≤ f_{3,r}(t) ≤ κ(r)`.

**Formalization Note** A centered Gaussian vector `(Y₀, …, Y_d)` with unit variances has law
`N(0, S)` with `S` its correlation matrix (positive semidefinite, unit diagonal, possibly
singular); the statement quantifies over all such `S` and is about `multivariateGaussian 0 S` on
`EuclideanSpace ℝ (Fin (d + 1))`. Coordinate `0` is the center `Y₀` and `Corr(Y₀, Yᵢ) = S 0 i`. -/
theorem proposition_8_8 (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (d : ℕ) (hd : d ≤ 3)
    (S : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) (hS : S.PosSemidef) (hdiag : ∀ i, S i i = 1)
    (hcorr : ∀ i, i ≠ 0 → r ≤ S 0 i) (t : ℝ) (ht : 0 ≤ t) :
    (multivariateGaussian 0 S).real {Y | t ≤ Y 0 ∧ ∃ i, i ≠ 0 ∧ Y i ≤ t} ≤ f3 r t ∧
      f3 r t ≤ kappa r := by sorry

end GaussianSweep
