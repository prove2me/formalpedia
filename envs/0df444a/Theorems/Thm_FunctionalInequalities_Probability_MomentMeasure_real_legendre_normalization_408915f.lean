-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_real_legendre_normalization_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:21.58868+00:00
-- url     : https://prove2.me/theorems/e3ecb1e2-5b5a-41d8-885b-662dbad3b665
-- title:
--   Real Representative Normalization
-- statement:
--   This is a normalization lemma for a finite real representative of a Legendre transform.
--
--   Let $E$ be a real inner-product space with Borel measurable structure, let $dx$ be a measure, let $q:E\to\overline{\mathbb{R}}$, and let $\psi:E\to\mathbb{R}$. Assume
--
--   $$
--   q^*(x)=\psi(x)\quad\text{in }\overline{\mathbb{R}}\text{ for every }x,
--   $$
--
--   and
--
--   $$
--   \operatorname{mass}_{dx}(q^*)=1.
--   $$
--
--   Then $e^{-\psi}$ is Bochner integrable with respect to $dx$, its integral is one, and the weighted measure `weightedMeasure dx (fun x => (ψ x : EReal))` is a probability measure:
--
--   $$
--   \int e^{-\psi(x)}\,dx=1.
--   $$
--
--   The declaration converts the finite extended-real conjugate mass into real integrability and probability normalization.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L264-L304 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization`; the repository is private at upload time).

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
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
section RealNormalization
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization_408915f
    (dx : Measure E) (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, legendre q x = (ψ x : EReal))
    (hmass : mass dx (legendre q) = 1) :
    Integrable (fun x => Real.exp (-ψ x)) dx ∧
    (∫ x, Real.exp (-ψ x) ∂dx) = 1 ∧
    IsProbabilityMeasure (weightedMeasure dx (fun x => (ψ x : EReal))) := by sorry
