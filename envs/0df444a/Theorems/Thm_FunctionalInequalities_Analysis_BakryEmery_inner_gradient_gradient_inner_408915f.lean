-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_gradient_gradient_inner_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:46.76111+00:00
-- url     : https://prove2.me/theorems/da65efd9-1199-4a3c-9325-10b16bbd2dd1
-- title:
--   Gradient Pairing Product-Rule Identity
-- statement:
--   This is a pointwise second-derivative identity for the drift term in the local Bochner calculation.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $U,f:E\to\mathbb R$ be respectively $C^2$, and let $x\in E$. Write $e_i$ for the fixed standard orthonormal basis of $E$. Then
--
--   $$
--   \left\langle \nabla f(x),\nabla\langle\nabla U,\nabla f\rangle(x)\right\rangle
--   =
--   D^2U(x)(\nabla f(x),\nabla f(x))
--   +\sum_i\sum_j \partial_iU(x)\,\partial_jf(x)\,D^2f(x)(e_i,e_j).
--   $$
--
--   The Hessian is represented by `bilinearIteratedFDerivTwo`, and the sums use `stdOrthonormalBasis ℝ E`. This technical identity is reusable in pointwise Bochner expansions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L262-L286 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
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
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Terms
variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner_408915f {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x : E) :
    ⟪gradient f x, gradient (fun y => ⟪gradient U y, gradient f y⟫) x⟫ =
      bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) +
        ∑ i, ∑ j, fderiv ℝ U x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j) := by sorry
