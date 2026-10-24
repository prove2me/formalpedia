-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tendsto_iteratedFDeriv_laplace_cond_closedBall_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:32.626822+00:00
-- url     : https://prove2.me/theorems/e156c390-25b5-43b2-afb1-6fe8683f940c
-- title:
--   Convergence of Truncated Laplace Derivatives
-- statement:
--   This statement proves convergence of the iterated derivatives of Laplace transforms of ball-conditioned measures.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\nu$ be a probability measure on $E$. Let $r>0$ and assume
--
--   $$
--   \int e^{r\|x\|}\,d\nu(x)<\infty.
--   $$
--
--   For each $d\in\mathbb N$, define the Laplace transform of the conditional measure on the closed ball $\overline B(0,R)$ by
--
--   $$
--   L_R(z)=\int e^{\langle z,x\rangle}\,d\bigl(\nu[\mid\overline B(0,R)]\bigr)(x),
--   $$
--
--   and let $L(z)=\int e^{\langle z,x\rangle}\,d\nu(x)$. Then, as $R\to\infty$ through natural numbers,
--
--   $$
--   D^dL_R(0)\longrightarrow D^dL(0).
--   $$
--
--   Here convergence is in the norm of the corresponding iterated derivative spaces. This is the moment-tensor convergence statement used in truncation arguments for cumulants.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L117-L155 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Local
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_LocalDerivatives
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
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
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
section CondHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.tendsto_iteratedFDeriv_laplace_cond_closedBall_408915f (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ) :
    Tendsto (fun R : ℕ => iteratedFDeriv ℝ d
        (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|Metric.closedBall (0 : E) R])) 0) atTop
      (𝓝 (iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0)) := by sorry
