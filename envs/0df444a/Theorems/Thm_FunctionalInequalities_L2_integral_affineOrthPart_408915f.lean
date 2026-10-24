-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affineOrthPart_408915f
-- name    : FunctionalInequalities.L2.integral_affineOrthPart_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:34.796935+00:00
-- url     : https://prove2.me/theorems/d8f52e53-bde3-4d55-aa29-d18e6a936ab5
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L184-L242 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affineOrthPart`; the repository is private at upload time).

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

theorem FunctionalInequalities.L2.integral_affineOrthPart_408915f (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : MemLp g 2 μ) :
    ∫ x, affineOrthPart μ g x ∂μ = 0 := by sorry
