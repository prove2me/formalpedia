-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_408915f
-- name    : FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:56.04582+00:00
-- url     : https://prove2.me/theorems/ebb76ba0-c236-4238-94b3-5648ed85f5e4
-- title:
--   Almost-Everywhere Constancy From Translation Invariance
-- statement:
--   This is a measurable translation-invariance criterion for almost-everywhere constancy.
--
--   Let $V$ be a finite-dimensional real inner-product normed additive group with its Borel measurable structure, and let $m$ be an additive Haar measure. For a measurable function $g:V\to\mathbb R$, assume that every translation preserves $g$ almost everywhere:
--
--   $$
--   \forall v\in V,\qquad g(x+v)=g(x)\quad\text{for $m$-almost every }x.
--   $$
--
--   Then there exists a constant $c\in\mathbb R$ such that
--
--   $$
--    g(x)=c\quad\text{for $m$-almost every }x.
--   $$
--
--   The Lean declaration is `exists_ae_eq_const_of_measurable_of_forall_ae_add_eq`. It is a reusable measure-theoretic auxiliary lemma; the conclusion is existential and only asserts equality almost everywhere.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/ZeroGradient.lean#L340-L370 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.ZeroGradient`, declaration `FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Measurable
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.Euclidean
end FunctionalInequalities.Energy.Euclidean
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_408915f {g : V → ℝ} (hg : Measurable g)
    (htr : ∀ v : V, ∀ᵐ x ∂m, g (x + v) = g x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, g x = c := by sorry
