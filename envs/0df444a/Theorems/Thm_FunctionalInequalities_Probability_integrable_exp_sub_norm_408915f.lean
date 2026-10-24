-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integrable_exp_sub_norm_408915f
-- name    : FunctionalInequalities.Probability.integrable_exp_sub_norm_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:37.49198+00:00
-- url     : https://prove2.me/theorems/1f3a0771-e0af-4766-a54a-98b93dfa84e3
-- title:
--   Haar Integrability Of Exponential Norm Decay
-- statement:
--   This is a finite-dimensional Haar-integrability estimate for exponential norm decay.
--
--   Let $E$ be finite-dimensional with a real inner product and Borel measurable structure, let $dx$ be an additive Haar measure on $E$, and let $c\in\mathbb R$ satisfy $c>0$. For every $M\in\mathbb R$,
--   $$y\longmapsto\exp(M-c\|y\|)$$
--   is integrable with respect to $dx$.
--
--   This supplies the integrable exponential envelope used in conjugate-mass estimates, including the zero-dimensional case.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L34-L60 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.integrable_exp_sub_norm`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Probability.integrable_exp_sub_norm_408915f [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (dx : Measure E) [dx.IsAddHaarMeasure] {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun y : E => Real.exp (M - c * ‖y‖)) dx := by sorry
