-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_readable
-- name    : FunctionalInequalities.L2.integral_affineOrthPart_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:53.042004+00:00
-- url     : https://prove2.me/theorems/c7437f0d-1782-4a2e-ab79-cc4f3f38eb24
-- title:
--   Zero Mean of the Affine Residual Under a Centered Law
-- statement:
--   This statement shows that the designated affine residual is centered under a centered probability measure.
--
--   Let $n\in\mathbb N$, $E=\mathbb R^n$ represented by `EuclideanSpace ℝ (Fin n)`, and let $e_j$ be its standard orthonormal basis. Assume:
--
--   1. $\mu$ is a probability measure on $E$, with $\operatorname{id}\in L^2(\mu)$.
--   2. $\int x\,d\mu(x)=0$.
--   3. $g:E\to\mathbb R$ belongs to $L^2(\mu)$.
--
--   Define the residual `L2.affineOrthPart` by
--   $$
--   h(x)=g(x)-\int g\,d\mu-\sum_{j\in\operatorname{Fin}(n)}\left(\int\langle e_j,y\rangle g(y)\,d\mu(y)\right)\langle e_j,x\rangle.
--   $$
--   Then
--   $$
--   \int h\,d\mu=0.
--   $$
--   This supplies the centering property of the concrete affine decomposition. Identity covariance is not required for this conclusion, and $n=0$ is included.
--
--   **Formalization Note** The $L^2$ hypotheses are `MemLp` hypotheses, including almost-everywhere strong measurability.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0) {g : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hg : MemLp g 2 μ) :
--       ∫ x, affineOrthPart μ g x ∂μ = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Previous: [`eLpNorm_le_eLpNorm_of_integral_sq_le`](https://prove2.me/theorems/a648c1d1-6bfd-4c14-9d9d-0b13ff8fe12d) · Next: [`memLp_affineOrthPart`](https://prove2.me/theorems/3bf6a5c9-eaa1-466d-aa39-eafd8f3964a0).
--
--   [Source excerpt, lines 185–188](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L185-L188) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L184-L242 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affineOrthPart`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_affineOrthPart_readable (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x ∂μ = 0 := by sorry
