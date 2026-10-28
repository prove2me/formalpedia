-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_sq_le_readable
-- name    : FunctionalInequalities.L2.integral_affineOrthPart_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:13.157987+00:00
-- url     : https://prove2.me/theorems/b462f885-9650-4c08-8d18-bf9383fa5a5b
-- title:
--   Squared-Integral Contraction of the Affine-Orthogonal Part
-- statement:
--   This lemma states Bessel's inequality for the concrete affine-orthogonal part.
--
--   Let $n\in\mathbb N$ and let $\mu$ be a probability measure on $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`). Assume:
--   1. $\operatorname{id}\in L^2(\mu)$ and $\int x\,d\mu=0$.
--   2. $\int\langle u,x\rangle\langle v,x\rangle\,d\mu=\langle u,v\rangle$ for all $u,v\in E$.
--   3. $g:E\to\mathbb R$ belongs to $L^2(\mu)$.
--
--   Using the standard orthonormal basis $(e_j)$, let $\widetilde g=$ `affineOrthPart` $\mu\ g$, namely
--   $$
--   \widetilde g(x)=g(x)-\int g\,d\mu-\sum_j\left(\int\langle e_j,y\rangle g(y)\,d\mu(y)\right)\langle e_j,x\rangle.
--   $$
--   Then
--   $$
--   \int\widetilde g^2\,d\mu\le\int g^2\,d\mu.
--   $$
--
--   This controls the squared $L^2$ size of the affine-orthogonal remainder under centered identity-covariance moment assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_affineOrthPart_sq_le (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
--       (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
--       {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
--       ∫ x, affineOrthPart μ g x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Supporting theorems: [`integral_affineOrthPart`](https://prove2.me/theorems/c7437f0d-1782-4a2e-ab79-cc4f3f38eb24), [`integral_inner_mul_affineOrthPart`](https://prove2.me/theorems/c43097da-d56f-42d1-8178-075a15d4e395), [`memLp_affineOrthPart`](https://prove2.me/theorems/3bf6a5c9-eaa1-466d-aa39-eafd8f3964a0).
--
--   Previous: [`integral_affineOrthPart_mul_sub`](https://prove2.me/theorems/d02bf2d3-cb86-4723-bceb-c6b16db784b1) · Next: [`integral_affine_sq`](https://prove2.me/theorems/8e6d6f95-c2c8-4475-91f6-ae7d05ba44fe).
--
--   [Source excerpt, lines 698–702](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L698-L702) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L697-L864 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affineOrthPart_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_affineOrthPart_sq_le_readable (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ := by sorry
