-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_mul_sub_408915f
-- name    : FunctionalInequalities.L2.integral_affineOrthPart_mul_sub_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:31:28.647402+00:00
-- url     : https://prove2.me/theorems/e64fd38f-62a3-4536-a2d7-5bc4780946ce
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L594-L695 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affineOrthPart_mul_sub`; the repository is private at upload time).

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

theorem FunctionalInequalities.L2.integral_affineOrthPart_mul_sub_408915f (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x * (g x - affineOrthPart μ g x) ∂μ = 0 := by sorry
