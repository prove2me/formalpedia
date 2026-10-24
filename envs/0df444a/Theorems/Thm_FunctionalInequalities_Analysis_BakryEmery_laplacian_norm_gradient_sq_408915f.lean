-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_laplacian_norm_gradient_sq_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:47.092209+00:00
-- url     : https://prove2.me/theorems/f5a39b5e-f3ec-4bd1-a7b1-9050ee9ed349
-- title:
--   Laplacian of the Squared Gradient Norm
-- statement:
--   This is the pointwise expansion of the Laplacian of the squared gradient norm.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $f:E\to\mathbb R$ be $C^3$, and let $x\in E$. For the fixed standard orthonormal basis $(e_i)$,
--
--   $$
--   \Delta\|\nabla f\|^2(x)
--   =
--   2\sum_i\sum_j\bigl(D^2f(x)(e_i,e_j)\bigr)^2
--   +2\sum_j \partial_jf(x)\sum_i\partial_i\partial_i\partial_jf(x).
--   $$
--
--   The Hessian terms are expressed by `bilinearIteratedFDerivTwo`; the third-order terms are retained explicitly. The identity is a technical component of the local Bochner identity and includes the dimension-zero case.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L207-L242 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq_408915f {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x =
      2 * ∑ i, ∑ j,
          (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j)) ^ 2 +
        2 * ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
            (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by sorry
