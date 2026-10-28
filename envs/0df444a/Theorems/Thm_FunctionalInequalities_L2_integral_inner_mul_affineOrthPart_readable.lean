-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_inner_mul_affineOrthPart_readable
-- name    : FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:45.725393+00:00
-- url     : https://prove2.me/theorems/c43097da-d56f-42d1-8178-075a15d4e395
-- title:
--   Orthogonality of the Affine Residual to Linear Functions
-- statement:
--   This statement gives orthogonality of the designated affine residual to every linear function.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $(e_j)_{j\in\operatorname{Fin}(n)}$ its standard orthonormal basis. Assume:
--
--   1. $\mu$ is a probability measure and $\operatorname{id}\in L^2(\mu)$.
--   2. $\int x\,d\mu(x)=0$.
--   3. For all $u,v\in E$, $\int\langle u,x\rangle\langle v,x\rangle\,d\mu(x)=\langle u,v\rangle$.
--   4. $g:E\to\mathbb R$ belongs to $L^2(\mu)$.
--
--   Set $h=$ `L2.affineOrthPart μ g`, explicitly
--   $$
--   h(x)=g(x)-\int g\,d\mu-\sum_j\left(\int\langle e_j,y\rangle g(y)\,d\mu(y)\right)\langle e_j,x\rangle.
--   $$
--   For every $u\in E$,
--   $$
--   \int\langle u,x\rangle h(x)\,d\mu(x)=0.
--   $$
--   This is the linear orthogonality property of the affine decomposition under centered identity-covariance moment assumptions. The $L^2$ assumptions are `MemLp` conditions, and no restriction $n>0$ is imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_inner_mul_affineOrthPart (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
--       (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
--       {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
--       ∫ x, ⟪u, x⟫ * affineOrthPart μ g x ∂μ = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Previous: [`memLp_affineOrthPart`](https://prove2.me/theorems/3bf6a5c9-eaa1-466d-aa39-eafd8f3964a0) · Next: [`sub_affineOrthPart_eq`](https://prove2.me/theorems/816eb15b-7e4e-4f5f-a7bc-08e3b253675d).
--
--   [Source excerpt, lines 274–278](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L274-L278) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L273-L477 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_inner_mul_affineOrthPart`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_readable (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪u, x⟫ * affineOrthPart μ g x ∂μ = 0 := by sorry
