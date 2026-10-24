-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_inner_eq_fderiv_logLaplace_of_lt_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:52.385764+00:00
-- url     : https://prove2.me/theorems/7c9ca2e3-2285-406f-a430-6669eef26e6e
-- title:
--   Tilted Linear Average as a Log-Laplace Derivative
-- statement:
--   This is the local tilt-average/derivative identity for linear observables.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $\mu$ be a finite nonzero measure, and assume that for some $r\in\mathbb R$,
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   If $z\in E$ satisfies $\|z\|<r$, then for every $v\in E$,
--
--   $$
--   \int \langle v,x\rangle\,d\mu_z(x)
--   =
--   D\Lambda_\mu(z)[v],
--   $$
--
--   where $\mu_z$ is the exponential tilt, $\Lambda_\mu=\logLaplace(\mu)$, and the derivative is represented by `fderiv ℝ (logLaplace μ) z v`. Only the single exponential moment at radius $r$ is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L176-L258 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
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
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section LaplaceCalculus
omit [CompleteSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_inner_eq_fderiv_logLaplace_of_lt_408915f (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    {r : ℝ} (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) {z : E} (hz : ‖z‖ < r) (v : E) :
    tiltAverage μ (fun x => ⟪v, x⟫) z = fderiv ℝ (logLaplace μ) z v := by sorry
