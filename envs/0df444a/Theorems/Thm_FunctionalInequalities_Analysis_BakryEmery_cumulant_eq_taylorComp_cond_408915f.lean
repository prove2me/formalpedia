-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_cumulant_eq_taylorComp_cond_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:49.209621+00:00
-- url     : https://prove2.me/theorems/2b26286e-0d67-4732-be00-86b58cbdc943
-- title:
--   Cumulants as Composed Taylor Jets
-- statement:
--   This identifies cumulants with the Faà di Bruno composition of the Taylor jets of the logarithm and the Laplace transform.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, and let $\mu$ be a probability measure. Let $r>0$ and assume
--
--   $$
--   \int e^{r\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   For every $k\in\mathbb N$,
--
--   $$
--   \kappa_k^\mu
--   =
--   \operatorname{TaylorComp}_k\!\left(
--   \operatorname{Taylor}(\log,1),
--   \operatorname{Taylor}\!\left(z\mapsto\int e^{\langle z,x\rangle}\,d\mu(x),0\right)
--   \right).
--   $$
--
--   In Lean this is the equality between `cumulant μ k` and `FormalMultilinearSeries.taylorComp` applied to the indicated `ftaylorSeriesWithin` objects. The statement is conditional on one positive exponential moment and applies to all orders $k$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L157-L207 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.cumulant_eq_taylorComp_cond_408915f (μ : Measure E) [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) μ) (k : ℕ) :
    cumulant μ k = (ftaylorSeriesWithin ℝ Real.log {0}ᶜ 1).taylorComp
      (ftaylorSeriesWithin ℝ (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂μ) (Metric.ball 0 r) 0) k := by sorry
