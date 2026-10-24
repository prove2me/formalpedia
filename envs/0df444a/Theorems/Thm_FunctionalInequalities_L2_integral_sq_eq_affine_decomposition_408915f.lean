-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_sq_eq_affine_decomposition_408915f
-- name    : FunctionalInequalities.L2.integral_sq_eq_affine_decomposition_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:31:29.97776+00:00
-- url     : https://prove2.me/theorems/0d0780da-3c0c-47a3-8c6c-741527abbce1
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L937-L1034 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_sq_eq_affine_decomposition`; the repository is private at upload time).

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

theorem FunctionalInequalities.L2.integral_sq_eq_affine_decomposition_408915f (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ =
      (∫ x, f x ∂μ) ^ 2 + ∑ j, (∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫ * f x ∂μ) ^ 2 +
        ∫ x, affineOrthPart μ f x ^ 2 ∂μ := by sorry
