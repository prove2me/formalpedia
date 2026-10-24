-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tendsto_cumulant_cond_closedBall_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:30.03401+00:00
-- url     : https://prove2.me/theorems/864988b6-883f-47fc-8abb-312a12167fa3
-- title:
--   Convergence of Cumulants Under Ball Conditioning
-- statement:
--   This formalizes the cumulant-convergence reduction associated with Theorem 4.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Theorem 4.1, p. 18.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel measurable structure, and let $\nu$ be a probability measure on $E$. Assume:
--
--   1. $r>0$.
--   2. $\int e^{r\|x\|}\,d\nu(x)<\infty$.
--   3. $k\in\mathbb N$.
--
--   For the conditional probability measure $\nu[\mid\overline B(0,R)]$ on the closed ball of radius $R$, its $k$th cumulant converges to the $k$th cumulant of $\nu$:
--
--   $$
--   \operatorname{cumulant}\bigl(\nu[\mid\overline B(0,R)]\bigr)_k
--   \longrightarrow
--   \operatorname{cumulant}(\nu)_k
--   \qquad(R\to\infty).
--   $$
--
--   The result is a technical truncation theorem that permits passage from compactly supported conditional laws to the original law in fixed cumulant order.
--
--   **Formalization Note** `cumulant` is a formal multilinear-series object. The conditioning is Lean's `ProbabilityTheory.cond` on `Metric.closedBall (0 : E) R`; the limit parameter is $R\in\mathbb N$.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L211-L251 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.tendsto_cumulant_cond_closedBall_408915f {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (k : ℕ) :
    Tendsto (fun R : ℕ => cumulant (ν[|Metric.closedBall (0 : E) R]) k) atTop
      (𝓝 (cumulant ν k)) := by sorry
