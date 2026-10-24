-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_integral_exp_inner_smul_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:42.126974+00:00
-- url     : https://prove2.me/theorems/d778a277-6f20-4458-8fd6-c2809044aea8
-- title:
--   Derivatives of Exponential Laplace-Type Integrals
-- statement:
--   This theorem identifies the iterated derivatives of a vector-valued Laplace-type integral with weighted moments.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $F$ be a complete real normed space, and let $\mu$ be a measure on $E$. Let $g:E\to F$ be strongly measurable almost everywhere with respect to $\mu$, and assume that for every $r\in\mathbb R$ the function $x\mapsto e^{r\|x\|}\|g(x)\|$ is integrable. For every $d\in\mathbb N$, $z\in E$, and $h:\operatorname{Fin}(d)\to E$, define $N(z)=\int e^{\langle z,x\rangle}g(x)\,d\mu(x)$.
--
--   $$D^dN(z)[h]=\int e^{\langle z,x\rangle}\left(\prod_{j} \langle x,h(j)\rangle\right)g(x)\,d\mu(x).$$
--
--   The result is a reusable differentiation-under-the-integral statement for exponential moments with values in a complete normed space.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L184-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul`; the repository is private at upload time).

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
section NormedSpace
variable {F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul_408915f (μ : Measure E) {g : E → F}
    (hg : AEStronglyMeasurable g μ)
    (hgi : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖) * ‖g x‖) μ) (d : ℕ) (z : E)
    (h : Fin d → E) :
    iteratedFDeriv ℝ d (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) z h =
      ∫ x, (Real.exp ⟪z, x⟫ * ∏ j, ⟪x, h j⟫) • g x ∂μ := by sorry
