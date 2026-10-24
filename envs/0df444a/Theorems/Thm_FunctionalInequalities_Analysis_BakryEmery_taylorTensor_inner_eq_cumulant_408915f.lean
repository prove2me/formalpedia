-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_inner_eq_cumulant_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:24.388181+00:00
-- url     : https://prove2.me/theorems/39d15d87-f677-4485-aa7c-9e0684065c03
-- title:
--   Taylor Tensor of a Linear Observable
-- statement:
--   This formalizes the linear-function identity from Proposition 7.1 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be a finite nonzero measure on a finite-dimensional real inner-product space $E$, assume that $e^{r\|x\|}$ is integrable for every $r\in\mathbb R$, and let $v\in E$, $d\in\mathbb N$, and $h:\operatorname{Fin}(d)\to E$. Then
--
--   $$T_d\bigl(x\mapsto\langle v,x\rangle\bigr)(h)
--   =\frac{1}{d!}\,\kappa_{d+1}(v,h_0,\ldots,h_{d-1}),$$
--
--   where `taylorTensor` is $T_d$ and `cumulant` is the $(d+1)$-st derivative tensor of the logarithmic Laplace transform at the origin.
--
--   This connects Taylor tensors of linear observables with cumulant tensors and is used in tensor-norm estimates.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L330-L354 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant_408915f (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (v : E) (d : ℕ)
    (h : Fin d → E) :
    taylorTensor μ (fun x => ⟪v, x⟫) d h = (d.factorial : ℝ)⁻¹ * cumulant μ (d + 1) (Fin.cons v h) := by sorry
