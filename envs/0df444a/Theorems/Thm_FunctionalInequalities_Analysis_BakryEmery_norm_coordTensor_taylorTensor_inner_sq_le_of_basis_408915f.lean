-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_coordTensor_taylorTensor_inner_sq_le_of_basis_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:25.383608+00:00
-- url     : https://prove2.me/theorems/538ec229-2b2c-441c-9819-0f99a3e7e9b6
-- title:
--   Coordinate Tensor Bound in an Arbitrary Orthonormal Basis
-- statement:
--   This formalizes the linear-function step cited on page 30 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Proposition 7.1.
--
--   Let $\mu$ be a probability measure on a finite-dimensional real inner-product space $E$ with all exponential moments. Let $b_E$ be an orthonormal basis indexed by $\operatorname{Fin}(m)$. Fix $d\in\mathbb N$, $b\in\mathbb R$, and assume that for every $u\in E$,
--
--   $$\sum_{J:\operatorname{Fin}(d)\to\operatorname{Fin}(m)}\kappa_{d+1}(u,b_E\circ J)^2\le b\|u\|^2.$$
--
--   Then for every $v\in E$,
--
--   $$\left\|\operatorname{coordTensor}_{b_E}\!\left(T_d(x\mapsto\langle v,x\rangle)\right)\right\|^2
--   \le \frac{b}{(d!)^2}\|v\|^2.$$
--
--   The result transfers a cumulant contraction estimate to the coordinate tensor of the Taylor tensor in any orthonormal basis.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean#L718-L755 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis_408915f (μ : Measure E) [IsProbabilityMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {m : ℕ}
    (bE : OrthonormalBasis (Fin m) ℝ E) {d : ℕ} {b : ℝ}
    (hR : ∀ u : E, ∑ J : Fin d → Fin m,
      cumulant μ (d + 1) (Fin.cons u fun k => bE (J k)) ^ 2 ≤ b * ‖u‖ ^ 2) (v : E) :
    ‖Analysis.Tensor.coordTensor bE (taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * ‖v‖ ^ 2 := by sorry
