-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_mul_sub_readable
-- name    : FunctionalInequalities.L2.integral_affineOrthPart_mul_sub_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:54.902434+00:00
-- url     : https://prove2.me/theorems/d02bf2d3-cb86-4723-bceb-c6b16db784b1
-- title:
--   Orthogonality Between the Affine Residual and Affine Part
-- statement:
--   This statement gives the vanishing cross term between a function's designated affine residual and its affine part.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $(e_j)$ its standard orthonormal basis. Assume:
--
--   1. $\mu$ is a probability measure and $\operatorname{id}\in L^2(\mu)$.
--   2. $\int x\,d\mu(x)=0$.
--   3. $\int\langle u,x\rangle\langle v,x\rangle\,d\mu(x)=\langle u,v\rangle$ for all $u,v\in E$.
--   4. $g:E\to\mathbb R$ belongs to $L^2(\mu)$.
--
--   Let $h=$ `L2.affineOrthPart μ g`, where
--   $$
--   h(x)=g(x)-\int g\,d\mu-\sum_j\left(\int\langle e_j,y\rangle g(y)\,d\mu(y)\right)\langle e_j,x\rangle.
--   $$
--   Then
--   $$
--   \int h(x)\bigl(g(x)-h(x)\bigr)\,d\mu(x)=0.
--   $$
--   This is the cross-term identity used in the affine Pythagorean decomposition. The $L^2$ hypotheses are `MemLp` conditions; dimension zero is included.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_affineOrthPart_mul_sub (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
--       (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
--       {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
--       ∫ x, affineOrthPart μ g x * (g x - affineOrthPart μ g x) ∂μ = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Supporting theorems: [`integral_affineOrthPart`](https://prove2.me/theorems/c7437f0d-1782-4a2e-ab79-cc4f3f38eb24), [`integral_inner_mul_affineOrthPart`](https://prove2.me/theorems/c43097da-d56f-42d1-8178-075a15d4e395), [`memLp_affineOrthPart`](https://prove2.me/theorems/3bf6a5c9-eaa1-466d-aa39-eafd8f3964a0).
--
--   Previous: [`contDiff_affineOrthPart`](https://prove2.me/theorems/222184b2-bf0f-4088-b7b6-1869ba885db6) · Next: [`integral_affineOrthPart_sq_le`](https://prove2.me/theorems/b462f885-9650-4c08-8d18-bf9383fa5a5b).
--
--   [Source excerpt, lines 595–599](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L595-L599) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L594-L695 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affineOrthPart_mul_sub`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_affineOrthPart_mul_sub_readable (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x * (g x - affineOrthPart μ g x) ∂μ = 0 := by sorry
