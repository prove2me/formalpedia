-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_exp_mul_norm_of_memLp_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:02:48.716484+00:00
-- url     : https://prove2.me/theorems/9c0da7c0-50cd-44d1-9090-c4469627a8da
-- title:
--   Exponential Weighted Integrability of an $L^2$ Function
-- statement:
--   This is an integrability lemma for square-integrable functions under exponential moment assumptions.
--
--   Let $E$ be a normed real space with a measurable Borel structure, let $\mu$ be a finite measure, and assume that every exponential norm weight is integrable:
--
--   $$
--   \forall s\in\mathbb R,
--   \quad \int e^{s\|x\|}\,d\mu(x)<\infty.
--   $$
--
--   If $f:E\to\mathbb R$ belongs to $L^2(\mu)$ and $r\in\mathbb R$, then
--
--   $$
--   \int e^{r\|x\|}\,\|f(x)\|\,d\mu(x)<\infty.
--   $$
--
--   The hypothesis is `MemLp f 2 μ`; no inner-product, finite-dimensional, or completeness assumption is required. This result is used to control weighted tilt integrals.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L250-L277 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
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

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
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
section IntegralCalculus
omit [CompleteSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.integrable_exp_mul_norm_of_memLp_408915f (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → ℝ} (hf : MemLp f 2 μ)
    (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖) * ‖f x‖) μ := by sorry
