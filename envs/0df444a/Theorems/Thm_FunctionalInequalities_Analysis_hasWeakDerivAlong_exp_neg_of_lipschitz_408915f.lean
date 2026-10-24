-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_exp_neg_of_lipschitz_408915f
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:23:42.097188+00:00
-- url     : https://prove2.me/theorems/b43ec67d-8533-428c-b2c0-445d1b214712
-- title:
--   Weak Derivative of a Negative Exponential
-- statement:
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $F:E\to\mathbb{R}$ be globally $L$-Lipschitz, and fix a direction $v\in E$. Then $e^{-F}$ has weak derivative along $v$ given by
--
--   $$
--   \partial_v(e^{-F})(x)=-e^{-F(x)}\,Df(x)[v],
--   $$
--
--   where $Df$ is represented by `fderiv`. Moreover, the derivative density belongs to $L^2$ on the restriction of Lebesgue measure to every compact set. No boundedness of $F$ or global integrability of $e^{-F}$ is required.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L564-L659 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz`; the repository is private at upload time).

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
universe u
section WeakNegativeExponential
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz_408915f {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {F : E → ℝ} {L : NNReal} (hF : LipschitzWith L F) (v : E) :
    HasWeakDerivAlong (fun x => Real.exp (-F x))
      (fun x => -Real.exp (-F x) * fderiv ℝ F x v) v ∧
    ∀ S : Set E, IsCompact S →
      MemLp (fun x => -Real.exp (-F x) * fderiv ℝ F x v) 2
        ((volume : Measure E).restrict S) := by sorry
