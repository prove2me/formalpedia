-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_sq_le_408915f
-- name    : FunctionalInequalities.L2.integral_affineOrthPart_sq_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:37:29.46179+00:00
-- url     : https://prove2.me/theorems/26292b8d-ccad-4530-a587-d733308c3ef4
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L697-L864 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affineOrthPart_sq_le`; the repository is private at upload time).

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

theorem FunctionalInequalities.L2.integral_affineOrthPart_sq_le_408915f (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ := by sorry
