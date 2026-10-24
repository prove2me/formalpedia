-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_hessianMatrixIn_posSemidef_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:46.25397+00:00
-- url     : https://prove2.me/theorems/070ba252-78ee-45f2-bf12-9335cdd75c95
-- title:
--   Positive Semidefinite Hessian Matrix
-- statement:
--   This theorem converts pointwise nonnegativity of a Hessian bilinear form into positive semidefiniteness of its matrix in an orthonormal basis.
--
--   Let $E$ be a real inner-product space, let $b$ be an orthonormal basis indexed by $\operatorname{Fin}(m)$, and let $\phi:E\to\mathbb R$. At $x\in E$, assume that $\phi$ is twice continuously differentiable and that
--
--   $$0\le D^2\phi(x)[v,v]\qquad\text{for every }v\in E.$$
--
--   Then the matrix `hessianMatrixIn φ b x` is positive semidefinite:
--
--   $$\operatorname{PosSemidef}(\operatorname{hessianMatrixIn}(\phi,b,x)).$$
--
--   This is a pointwise linear-algebraic bridge between the Hessian form and its coordinate matrix.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean#L217-L241 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.MongeAmpere`, declaration `FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Group.Matrix

noncomputable section
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open Filter Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
section Positivity
omit [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef_408915f {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x)
    (hH : ∀ v : E, 0 ≤ bilinearIteratedFDerivTwo ℝ φ x v v) :
    (hessianMatrixIn φ b x).PosSemidef := by sorry
