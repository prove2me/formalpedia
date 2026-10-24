-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_eq_zero_of_growth_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:32.119986+00:00
-- url     : https://prove2.me/theorems/360ad0d4-0f9a-4e37-89e5-423b2eaad44f
-- title:
--   Vanishing Integral of the Weighted Laplacian
-- statement:
--   This theorem states the generator identity for a function with polynomial growth.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $V,f:E\to\mathbb R$. Assume:
--
--   1. $V$ is $C^1$.
--   2. There are $C_V\in\mathbb R$ and $k_V\in\mathbb N$ such that $\|\nabla V(x)\|\le C_V(1+\|x\|)^{k_V}$.
--   3. Every exponential moment is integrable with respect to $m.\operatorname{tilted}(-V)$.
--   4. $f$ is $C^2$ and, for some $C\in\mathbb R$ and $k\in\mathbb N$, the functions $f$, $D f$, and $D^2f$ all have norm bounded by $C(1+\|x\|)^k$ pointwise, with the value bound stated using $|f(x)|$.
--
--   Then, writing $\mathcal L=\operatorname{weightedLaplacian}(V,\cdot)$,
--
--   $$\int \mathcal Lf\,d\bigl(m.\operatorname{tilted}(-V)\bigr)=0.$$
--
--   This is the polynomial-growth version of the weighted generator identity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L355-L476 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Distribution.TemperateGrowth
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

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
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
variable (m : Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth_408915f {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : ContDiff ℝ 2 f) {C : ℝ} {k : ℕ}
    (hfg : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ k ∧ ‖iteratedFDeriv ℝ 1 f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, weightedLaplacian V f x ∂(m.tilted (-V)) = 0 := by sorry
