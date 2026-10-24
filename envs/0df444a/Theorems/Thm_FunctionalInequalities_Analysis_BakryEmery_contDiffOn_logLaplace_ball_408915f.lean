-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiffOn_logLaplace_ball_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:55.312622+00:00
-- url     : https://prove2.me/theorems/7d22b540-9751-4066-a9ca-ba4a31ad4d1f
-- title:
--   Smoothness of the Log-Laplace Transform on a Ball
-- statement:
--   This is the local smoothness statement for the log-Laplace transform, corresponding to the finite-and-smooth assertion in Bizeul–Klartag–Lehec, p. 29.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $\mu$ be a finite nonzero measure on $E$, and let $r>0$. Assume
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   Then the log-Laplace transform
--   $\Lambda_\mu(z)=\log\int e^{\langle z,x\rangle}\,d\mu(x)$ is $C^\infty$ on the open ball $B(0,r)$:
--
--   $$
--   \Lambda_\mu\in C^\infty(B(0,r)).
--   $$
--
--   The nonzero condition is represented by the `NeZero μ` instance, and finiteness by `IsFiniteMeasure μ`. The conclusion is `ContDiffOn ℝ ∞ (logLaplace μ)` on the ball.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L757-L791 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball`; the repository is private at upload time).

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
section CumulantEstimates
omit [CompleteSpace E]
open scoped ContDiff

theorem FunctionalInequalities.Analysis.BakryEmery.contDiffOn_logLaplace_ball_408915f (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ] {r : ℝ}
    (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) :
    ContDiffOn ℝ ∞ (logLaplace μ) (Metric.ball 0 r) := by sorry
