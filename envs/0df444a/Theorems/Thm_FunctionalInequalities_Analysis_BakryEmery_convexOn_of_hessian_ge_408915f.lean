-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_convexOn_of_hessian_ge_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:51.049253+00:00
-- url     : https://prove2.me/theorems/39d5653e-4929-4c72-b888-678e4fe44eca
-- title:
--   Convexity from a Nonnegative Hessian Lower Bound
-- statement:
--   This is the standard convexity implication from a pointwise Hessian lower bound.
--
--   Let $E$ be a real inner-product space and let $U:E\to\mathbb R$ be $C^2$. Let $\rho\geq0$ and suppose that for every $x,v\in E$,
--
--   $$
--   \rho\,\|v\|^2\leq D^2U(x)(v,v).
--   $$
--
--   Then $U$ is convex on all of $E$:
--
--   $$
--   U\text{ is convex on }E.
--   $$
--
--   The Hessian is represented by `bilinearIteratedFDerivTwo`, and no completeness or finite-dimensionality assumption is required. The result may be used to convert curvature-type Hessian hypotheses into global convexity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean#L37-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Curvature`, declaration `FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory InnerProductSpace
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge_408915f {U : E → ℝ} (hU : ContDiff ℝ 2 U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ConvexOn ℝ Set.univ U := by sorry
