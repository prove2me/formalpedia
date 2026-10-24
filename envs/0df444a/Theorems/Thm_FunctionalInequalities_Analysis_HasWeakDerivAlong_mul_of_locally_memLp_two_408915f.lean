-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_memLp_two_408915f
-- name    : FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:56.221871+00:00
-- url     : https://prove2.me/theorems/89265818-a380-4e55-89c2-adc713ad6110
-- title:
--   Weak Product Rule with Bounded Factors and Local Derivative Control
-- statement:
--   This is a localized weak product rule with globally essentially bounded factors. It is listed as a partial formalization of Theorem 2.5 of Letwin2026.
--
--   Let $n\in\mathbb{N}$, let $f,df,g,dg$ be real-valued functions on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$, and let $v$ be a vector. Assume:
--
--   1. $f$ has weak derivative $df$ along $v$, and $g$ has weak derivative $dg$ along $v$.
--   2. $f$ and $g$ belong to global $L^\infty(\operatorname{volume})$, represented by `MemLp` exponent $\top$.
--   3. For every compact $S$, $df,dg\in L^2(\operatorname{volume}|_S)$.
--
--   Then the product has weak derivative
--
--   $$x\mapsto df(x)g(x)+f(x)dg(x),$$
--
--   and this derivative belongs to $L^2(\operatorname{volume}|_S)$ for every compact $S$. This is a compact-local product theorem.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L209-L344 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory
open scoped ContDiff
section WeakProducts
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two_408915f {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf_top : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg_top : MemLp g (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
