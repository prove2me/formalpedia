-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_sub_affineOrthPart_eq_408915f
-- name    : FunctionalInequalities.L2.sub_affineOrthPart_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:37:28.121001+00:00
-- url     : https://prove2.me/theorems/1c2c6dd2-daae-47c1-944f-308888f72729
-- title:
--   Subtracting an Affine-Orthogonal Part From an Orthogonal Function
-- statement:
--   This lemma gives an exact function identity for affine subtraction when the first function is orthogonal to affine functions.
--
--   Let $n\in\mathbb N$, $E=\mathbb R^n$ (`EuclideanSpace ℝ (Fin n)`), and $\mu$ a probability measure on $E$. Assume:
--   1. $\operatorname{id}\in L^2(\mu)$.
--   2. $f,g:E\to\mathbb R$ belong to $L^2(\mu)$.
--   3. $\int f\,d\mu=0$ and $\int\langle u,x\rangle f(x)\,d\mu=0$ for every $u\in E$.
--
--   For any function $h$, write $\widetilde h=$ `affineOrthPart` $\mu\ h$, defined by subtracting $\int h\,d\mu$ and $\sum_j(\int\langle e_j,y\rangle h(y)\,d\mu(y))\langle e_j,\cdot\rangle$, where $(e_j)$ is the standard orthonormal basis. Then, as functions on $E$,
--   $$
--   f-\widetilde g=\widetilde{\,f-g\,}.
--   $$
--
--   This identity is useful for comparing affine-subtracted approximations. It is pointwise, not merely almost everywhere, and requires neither centering nor identity covariance of $\mu$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L479-L527 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.sub_affineOrthPart_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.L2.sub_affineOrthPart_eq_408915f (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) (hg : MemLp g 2 μ) :
    f - affineOrthPart μ g = affineOrthPart μ (f - g) := by sorry
