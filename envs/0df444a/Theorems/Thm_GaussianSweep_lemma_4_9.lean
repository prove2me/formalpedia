-- Prove2me | Theorems.Thm_GaussianSweep_lemma_4_9
-- name    : GaussianSweep.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:05.652499+00:00
-- url     : https://prove2.me/theorems/e8b34196-0b10-4793-a574-830a48a12519
-- title:
--   Lemma 4.9 — Sheppard's formula for two and three coordinates
-- statement:
--   Let $(X_1, X_2, X_3)$ be a centered Gaussian vector with unit variances and put $\vartheta_{ij} = \arccos \mathrm{Corr}(X_i, X_j) \in [0, \pi]$. Then
--   $$
--   \mathbb P(\operatorname{sgn} X_1 \ne \operatorname{sgn} X_2) = \frac{\vartheta_{12}}{\pi}, \qquad
--   \mathbb P(X_1 > 0, X_2 > 0) = \frac12 - \frac{\vartheta_{12}}{2\pi} = \frac14 + \frac{\arcsin \mathrm{Corr}(X_1, X_2)}{2\pi},
--   $$
--   and
--   $$
--   \mathbb P(X_1 > 0, X_2 > 0, X_3 > 0) = \frac12 - \frac{\vartheta_{12} + \vartheta_{13} + \vartheta_{23}}{4\pi}.
--   $$
--   These orthant formulas at threshold zero give the closed form $\kappa(r)$ of the ideal star function at zero.
--
--   **Formalization Note** The vector is given through its law $N(0, S)$, $S$ a correlation matrix, possibly singular; coordinates are indexed $0, 1, 2$ and $\mathrm{Corr}(X_i, X_j) = S_{ij}$. The sign is the real sign function ($0$ at $0$; the event $X_i = 0$ is null).
--
--   Differences from the source:
--   - encoding: a centered Gaussian vector (X₁, X₂, X₃) with unit variances → its law multivariateGaussian 0 S, quantified over every positive semidefinite S with unit diagonal (singular allowed); reason: the law of a centered Gaussian vector is N(0, S) for its covariance S, and the events depend only on the law
--   - encoding: sgn → Real.sign (value 0 at 0); reason: each X_i is nonzero almost surely, so the events agree up to a null set
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 4.9, p.26 (PDF p.28)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace GaussianSweep

/-- Lemma 4.9 (Sheppard's formula) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 4.9, p.26 (PDF p.28)). Let `(X₁, X₂, X₃)` be
centered Gaussian with unit variances and `ϑᵢⱼ = arccos Corr(Xᵢ, Xⱼ) ∈ [0, π]`. Then
`P(sgn X₁ ≠ sgn X₂) = ϑ₁₂/π`, `P(X₁ > 0, X₂ > 0) = 1/2 − ϑ₁₂/(2π) = 1/4 + arcsin Corr(X₁, X₂)/(2π)`,
and `P(X₁ > 0, X₂ > 0, X₃ > 0) = 1/2 − (ϑ₁₂ + ϑ₁₃ + ϑ₂₃)/(4π)`.

**Formalization Note** A centered Gaussian vector with unit variances has law `N(0, S)` with `S`
its correlation matrix (positive semidefinite, unit diagonal, possibly singular); the statement is
about `multivariateGaussian 0 S` on `EuclideanSpace ℝ (Fin 3)`, with 0-based coordinates, and
`Corr(Xᵢ, Xⱼ) = S i j`. `sgn` is `Real.sign` (`0` at `0`; the event `Xᵢ = 0` is null). -/
theorem lemma_4_9 (S : Matrix (Fin 3) (Fin 3) ℝ) (hS : S.PosSemidef) (hdiag : ∀ i, S i i = 1) :
    (multivariateGaussian 0 S).real {X | Real.sign (X 0) ≠ Real.sign (X 1)} =
        Real.arccos (S 0 1) / Real.pi ∧
    (multivariateGaussian 0 S).real {X | 0 < X 0 ∧ 0 < X 1} =
        1 / 2 - Real.arccos (S 0 1) / (2 * Real.pi) ∧
    1 / 2 - Real.arccos (S 0 1) / (2 * Real.pi) = 1 / 4 + Real.arcsin (S 0 1) / (2 * Real.pi) ∧
    (multivariateGaussian 0 S).real {X | 0 < X 0 ∧ 0 < X 1 ∧ 0 < X 2} =
        1 / 2 - (Real.arccos (S 0 1) + Real.arccos (S 0 2) + Real.arccos (S 1 2)) /
          (4 * Real.pi) := by sorry

end GaussianSweep
