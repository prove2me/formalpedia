-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_inner_mul_affineOrthPart_408915f
-- name    : FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:34.772047+00:00
-- url     : https://prove2.me/theorems/cf583fb2-7107-47d5-9292-0c080ebb5f22
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L273-L477 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_inner_mul_affineOrthPart`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section AffineOrthPart
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_inner_mul_affineOrthPart_408915f (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) (u : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ⟪u, x⟫ * affineOrthPart μ g x ∂μ = 0 := by sorry
