-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_408915f
-- name    : FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:29.116798+00:00
-- url     : https://prove2.me/theorems/30726d64-72f8-4453-968b-16df2319c646
-- title:
--   Weak Integration By Parts For The Weighted Laplacian
-- statement:
--   This formalizes part of Lemma A.6 of Letwin (arXiv:2607.24164v1), whose reviewed paper statement is the Brascamp–Lieb inequality for the tilted law.
--
--   Let n be a natural number and work on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$. Let U be C¹, let v be smooth, and assume v has compact support. Normalize the exponential weight by
--
--   $$\int_E e^{-U(x)}\,dx=1.$$
--
--   Let η be locally integrable and globally bounded by C in norm. For each coordinate i, suppose η has weak derivative aᵢ along the i-th Euclidean basis direction, and suppose every aᵢ belongs locally to $L^2$ on compact sets. Then both functions
--
--   $$x\mapsto \eta(x)\,\mathcal L_Uv(x)$$
--
--   and
--
--   $$x\mapsto\sum_i a_i(x)\,D_{e_i}v(x)$$
--
--   are integrable with respect to the tilted measure $d\nu=e^{-U}dx$, and
--
--   $$\int \eta\,\mathcal L_Uv\,d\nu=-\int\sum_i a_iD_{e_i}v\,d\nu.$$
--
--   Here $\mathcal L_Uv=\Delta v-\langle\nabla U,\nabla v\rangle$ is the ordinary weighted Laplacian.
--
--   The declaration is a rough integration-by-parts tool for compactly supported tests and weakly differentiable bounded multipliers.
--
--   **Formalization Note** The conclusion is stated for all n, including n=0; the tilted measure is formed from volume measure and the function −U.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakLaplacian.lean#L21-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakLaplacian`, declaration `FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ContDiff Topology RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.integral_bounded_weak_mul_weightedLaplacian_of_contDiff_one_408915f {n : ℕ}
    {U v eta : EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : ContDiff ℝ 1 U) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (hnorm : (∫ x, Real.exp (-U x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1)
    (a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ)
    (heta : LocallyIntegrable eta (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖eta x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong eta (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    Integrable (fun x => eta x * weightedLaplacian U v x)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    Integrable (fun x => ∑ i : Fin n, a i x *
      fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U)) ∧
    (∫ x, eta x * weightedLaplacian U v x
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) =
      -(∫ x, (∑ i : Fin n, a i x * fderiv ℝ v x (EuclideanSpace.basisFun (Fin n) ℝ i))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-U))) := by sorry
