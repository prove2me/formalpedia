-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_one_apply_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:27.066875+00:00
-- url     : https://prove2.me/theorems/ef38f6e8-2c58-4323-ac8f-c35ca1c24df3
-- title:
--   First Taylor Tensor as a Centered Moment
-- statement:
--   This formalizes the centered first-moment formula for the first Taylor tensor.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$. Assume:
--
--   1. For every $r\in\mathbb R$, $x\mapsto e^{r\|x\|}$ is integrable with respect to $\mu$.
--   2. $f:E\to\mathbb R$ belongs to $L^2(\mu)$.
--   3. $w\in E$.
--
--   Writing $T_d f$ for `taylorTensor μ f d`, the first tensor evaluated at $w$ satisfies
--
--   $$
--   T_1f(w)=\int \langle w,x\rangle f(x)\,d\mu(x)
--   -\left(\int f\,d\mu\right)\left(\int \langle w,x\rangle\,d\mu(x)\right).
--   $$
--
--   This identifies the first Taylor tensor with the centered first moment and provides the degree-one case used in tensor and cumulant calculations.
--
--   **Formalization Note** The measure is a probability measure, and all displayed integrals are ordinary real-valued integrals under the stated integrability consequences of the hypotheses.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/LocalDerivatives.lean#L166-L257 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.LocalDerivatives`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
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
import Mathlib.Probability.Moments.IntegrableExpMul

open MeasureTheory Filter Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_apply_408915f (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ}
    (hf : MemLp f 2 μ) (w : E) :
    taylorTensor μ f 1 (fun _ => w) =
      (∫ x, ⟪w, x⟫ * f x ∂μ) - (∫ x, f x ∂μ) * ∫ x, ⟪w, x⟫ ∂μ := by sorry
