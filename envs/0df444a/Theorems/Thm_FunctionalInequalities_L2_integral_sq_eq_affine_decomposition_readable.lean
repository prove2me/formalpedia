-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_sq_eq_affine_decomposition_readable
-- name    : FunctionalInequalities.L2.integral_sq_eq_affine_decomposition_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:00.333985+00:00
-- url     : https://prove2.me/theorems/77f34311-b8ed-4189-84bc-10fd3772875b
-- title:
--   Pythagorean Identity for the Concrete Affine Decomposition
-- statement:
--   This statement gives the Pythagorean identity for the concrete affine decomposition in $L^2$.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $(e_j)$ its standard orthonormal basis. Assume:
--
--   1. $\mu$ is a probability measure and $\operatorname{id}\in L^2(\mu)$.
--   2. $\int x\,d\mu(x)=0$.
--   3. For all $u,v\in E$, $\int\langle u,x\rangle\langle v,x\rangle\,d\mu(x)=\langle u,v\rangle$.
--   4. $f:E\to\mathbb R$ belongs to $L^2(\mu)$.
--
--   Write $c=\int f\,d\mu$, $a_j=\int\langle e_j,x\rangle f(x)\,d\mu(x)$, and $h(x)=f(x)-c-\sum_j a_j\langle e_j,x\rangle$, the residual `L2.affineOrthPart μ f`. Then
--   $$
--   \int f^2\,d\mu=c^2+\sum_{j\in\operatorname{Fin}(n)}a_j^2+\int h^2\,d\mu.
--   $$
--   This separates the squared $L^2$ size into constant, linear, and residual contributions. All $L^2$ hypotheses are `MemLp` conditions, and all natural dimensions are included.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_sq_eq_affine_decomposition (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
--       (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) :
--       ∫ x, f x ^ 2 ∂μ =
--         (∫ x, f x ∂μ) ^ 2 + ∑ j, (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x ∂μ) ^ 2 +
--           ∫ x, affineOrthPart μ f x ^ 2 ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Supporting theorems: [`integral_affineOrthPart_mul_sub`](https://prove2.me/theorems/d02bf2d3-cb86-4723-bceb-c6b16db784b1), [`integral_affine_sq`](https://prove2.me/theorems/8e6d6f95-c2c8-4475-91f6-ae7d05ba44fe), [`memLp_affineOrthPart`](https://prove2.me/theorems/3bf6a5c9-eaa1-466d-aa39-eafd8f3964a0).
--
--   Previous: [`integral_affine_sq`](https://prove2.me/theorems/8e6d6f95-c2c8-4475-91f6-ae7d05ba44fe).
--
--   [Source excerpt, lines 938–944](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L938-L944) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L937-L1034 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_sq_eq_affine_decomposition`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_sq_eq_affine_decomposition_readable (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ =
      (∫ x, f x ∂μ) ^ 2 + ∑ j, (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x ∂μ) ^ 2 +
        ∫ x, affineOrthPart μ f x ^ 2 ∂μ := by sorry
