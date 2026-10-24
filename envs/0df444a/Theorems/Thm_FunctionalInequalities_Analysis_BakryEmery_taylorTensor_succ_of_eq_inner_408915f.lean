-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_succ_of_eq_inner_408915f
-- name    : FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:31.346981+00:00
-- url     : https://prove2.me/theorems/ea631f01-76a1-4992-ba7c-1c4cdcedf15a
-- title:
--   Successor Taylor Tensor from an Inner-Product Identity
-- statement:
--   This statement formalizes the tensor identity corresponding to Lemma 3.6 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a real inner-product space that is complete and measurable, let $\mu$ be a measure on $E$, and let $g:E\to\mathbb R$ and $G:E\to E$. Assume:
--
--   1. The tilt average $F_G=\operatorname{tiltAverage}(\mu,G)$ is infinitely continuously differentiable.
--   2. The tilt average of $g$ satisfies, for every $w\in E$,
--      $$
--      F_g(w)=\langle w,F_G(w)\rangle.
--      $$
--   3. $d\in\mathbb N$.
--
--   Then
--
--   $$
--   T_{d+1}g=\operatorname{symmetrizeML}\bigl(\operatorname{appendInner}(T_dG)\bigr).
--   $$
--
--   The result isolates the tensor consequence of the tilt identity and can be reused independently of compact-support assumptions used elsewhere.
--
--   **Formalization Note** The statement has no finite-dimensionality or Borel-space hypothesis. The definitions `tiltAverage`, `taylorTensor`, `appendInner`, and `symmetrizeML` are used exactly as Lean defines them.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean#L691-L733 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable`, declaration `FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner`; the repository is private at upload time).

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
section Lp
omit [FiniteDimensional ℝ E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner_408915f (μ : Measure E) {g : E → ℝ} {G : E → E}
    (hG : ContDiff ℝ ∞ (tiltAverage μ G))
    (hEq : tiltAverage μ g = fun w => ⟪w, tiltAverage μ G w⟫) (d : ℕ) :
    taylorTensor μ g (d + 1) = symmetrizeML (appendInner (taylorTensor μ G d)) := by sorry
