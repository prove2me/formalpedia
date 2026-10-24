-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_gradient_gradient_laplacian_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:58.465037+00:00
-- url     : https://prove2.me/theorems/0efa05e8-3d84-4537-af5c-15d66b00a2de
-- title:
--   Gradient Pairing with the Laplacian
-- statement:
--   This is a pointwise third-order derivative identity.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $f:E\to\mathbb R$ be $C^3$, and let $x\in E$. With $e_i$ denoting the fixed standard orthonormal basis,
--
--   $$
--   \langle\nabla f(x),\nabla(\Delta f)(x)\rangle
--   =
--   \sum_j \partial_jf(x)\sum_i \partial_i\partial_i\partial_j f(x).
--   $$
--
--   In the formal expression, the inner sum is written by applying the derivative to $y\mapsto \partial_i\partial_j f(y)$ in the direction $e_i$; equality uses commutation of third derivatives. This is an auxiliary identity for local Bochner formulas.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L244-L260 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian_408915f {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    ⟪gradient f x, gradient (Laplacian.laplacian f) x⟫ =
      ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
          (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by sorry
