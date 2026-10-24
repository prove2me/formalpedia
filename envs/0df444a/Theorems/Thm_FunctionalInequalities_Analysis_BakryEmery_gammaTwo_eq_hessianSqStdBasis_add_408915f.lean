-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_gammaTwo_eq_hessianSqStdBasis_add_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:50.089711+00:00
-- url     : https://prove2.me/theorems/9de93c0b-8a96-4953-988e-41731145a31e
-- title:
--   Standard-Basis Bochner Identity
-- statement:
--   This formalizes the pointwise Bochner identity in the fixed standard orthonormal basis.
--
--   Let $E$ be a complete finite-dimensional real inner-product space, let $U:E\to\mathbb R$ be $C^2$, let $f:E\to\mathbb R$ be $C^3$, and let $x\in E$. Then
--
--   $$
--   \Gamma_2(U,f)(x)
--   =
--   \operatorname{HessSq}_{\mathrm{std}}(f)(x)
--   +D^2U(x)(\nabla f(x),\nabla f(x)).
--   $$
--
--   Here `gammaTwo U f` is the pointwise carré-du-champ iteration, and `hessianSqStdBasis f x` is the sum of squares of the Hessian entries in the fixed basis $(e_i)$:
--   $\operatorname{HessSq}_{\mathrm{std}}(f)=\sum_{i,j}(D^2f(e_i,e_j))^2$.
--
--   This is the central local identity used to derive nonnegativity and curvature estimates; it asserts a standard-basis formula, not basis independence.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean#L296-L313 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add`; the repository is private at upload time).

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
section Bochner
variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add_408915f {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (x : E) :
    gammaTwo U f x =
      hessianSqStdBasis f x +
        bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) := by sorry
