-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_iteratedFDeriv_laplace_cond_sub_le_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:33.178481+00:00
-- url     : https://prove2.me/theorems/ce6d703f-116c-4aa8-ac7a-9aade370bc5c
-- title:
--   Conditional Versus Unconditional Laplace Derivative Bound
-- statement:
--   This is an operator-norm estimate for moment tensors of a conditional measure.
--
--   Let $\nu$ be a probability measure on a finite-dimensional real inner-product space $E$, let $r>0$, and assume $e^{r\|x\|}$ is integrable with respect to $\nu$. Let $s\subseteq E$ be measurable with $\nu(s)\ne0$. For every $d\in\mathbb N$,
--
--   $$\left\|D^d\!\left(z\mapsto\int e^{\langle z,x\rangle}\,d\nu[\mid s](x)\right)(0)
--   -D^d\!\left(z\mapsto\int e^{\langle z,x\rangle}\,d\nu(x)\right)(0)\right\|
--   $$
--   $$\le \left|\bigl(\nu(s)^{-1}\bigr).\operatorname{toReal}-1\right|\int\|x\|^d\,d\nu(x)+\int_{s^c}\|x\|^d\,d\nu(x).$$
--
--   Here $\nu[\mid s]$ is the conditional probability measure on $s$. The estimate quantifies the change in Laplace derivative tensors under conditioning.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean#L58-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Truncation`, declaration `FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_cond_sub_le_408915f (ν : Measure E) [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hexp : Integrable (fun x => Real.exp (r * ‖x‖)) ν) (d : ℕ)
    {s : Set E} (hs : MeasurableSet s) (hs0 : ν s ≠ 0) :
    ‖iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂(ν[|s])) 0 -
        iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ ∂ν) 0‖ ≤
      |((ν s)⁻¹).toReal - 1| * ∫ x, ‖x‖ ^ d ∂ν + ∫ x in sᶜ, ‖x‖ ^ d ∂ν := by sorry
