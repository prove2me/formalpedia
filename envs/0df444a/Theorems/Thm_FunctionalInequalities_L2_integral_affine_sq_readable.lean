-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affine_sq_readable
-- name    : FunctionalInequalities.L2.integral_affine_sq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:48.510983+00:00
-- url     : https://prove2.me/theorems/8e6d6f95-c2c8-4475-91f6-ae7d05ba44fe
-- title:
--   Square Integral of an Affine Function Under Isotropic Moment Conditions
-- statement:
--   This statement evaluates the square integral of an affine function under centered identity-covariance moment assumptions.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $e_j=$ `EuclideanSpace.basisFun (Fin n) ℝ j`. Assume:
--
--   1. $\mu$ is a probability measure and $\operatorname{id}\in L^2(\mu)$ (`MemLp`).
--   2. $\int x\,d\mu(x)=0$.
--   3. For every $u,v\in E$, $\int\langle u,x\rangle\langle v,x\rangle\,d\mu(x)=\langle u,v\rangle$.
--
--   For every $c\in\mathbb R$ and coefficient family $a:\operatorname{Fin}(n)\to\mathbb R$,
--   $$
--   \int\left(c+\sum_{j\in\operatorname{Fin}(n)}a_j\langle e_j,x\rangle\right)^2\,d\mu(x)
--   =c^2+\sum_{j\in\operatorname{Fin}(n)}a_j^2.
--   $$
--   This identifies the $L^2$ square of the affine part with the Euclidean square of its coefficients. No log-concavity or positive-dimension assumption is needed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.L2`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_affine_sq (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
--       (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
--       (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
--       (c : ℝ) (a : Fin n → ℝ) :
--       ∫ x, (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2 ∂μ =
--         c ^ 2 + ∑ j, a j ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`L2/AffineDecomposition`](https://prove2.me/theorems/78e08949-2f1e-4981-ab20-7428c8af6614).
--
--   Previous: [`integral_affineOrthPart_sq_le`](https://prove2.me/theorems/b462f885-9650-4c08-8d18-bf9383fa5a5b) · Next: [`integral_sq_eq_affine_decomposition`](https://prove2.me/theorems/77f34311-b8ed-4189-84bc-10fd3772875b).
--
--   [Source excerpt, lines 881–886](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L881-L886) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L880-L935 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affine_sq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_L2_AffineDecomposition

open MeasureTheory
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_affine_sq_readable (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ x, (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2 ∂μ =
      c ^ 2 + ∑ j, a j ^ 2 := by sorry
