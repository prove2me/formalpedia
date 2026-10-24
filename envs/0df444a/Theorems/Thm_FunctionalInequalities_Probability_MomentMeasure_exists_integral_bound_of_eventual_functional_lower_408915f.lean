-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_integral_bound_of_eventual_functional_lower_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:37.141577+00:00
-- url     : https://prove2.me/theorems/2c5feb62-2e8c-4b71-8264-a9652ec243b2
-- title:
--   Integral Bounds From An Eventual Functional Lower Bound
-- statement:
--   This is the normalized-sequence integral-control statement corresponding to estimate (62) in the coercivity framework.
--
--   Let $E$ be finite-dimensional with additive Haar measure $dx$, and let $\mu$ be a probability measure satisfying:
--
--   1. Every linear subspace with full $\mu$-measure equals $E$.
--   2. The identity map is $\mu$-integrable.
--   3. $\int x\,d\mu(x)=0$.
--
--   Let $\phi_j:E\to\overline{\mathbb R}$ be a sequence such that every $\phi_j\ge0$, $\phi_j(0)=0$, `ConvexPotential (φ j)`, and `PotentialIntegrable (φ j) μ`. If, for some $b\in\mathbb R$, eventually in $j$,
--   $$b\le\operatorname{variationalFunctional}(dx,\mu,\phi_j),$$
--   then there exists $B\ge0$ such that
--   $$\int_E(\phi_j(x)).\operatorname{toReal}\,d\mu(x)\le B\quad\text{for every }j,$$
--   and
--   $$\sup_j\int^-_E(\phi_j(x)).\operatorname{toENNReal}\,d\mu(x)\ne+\infty.$$
--
--   The bound includes the finite initial segment of the sequence.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean#L243-L270 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Coercivity`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
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
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower_408915f
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (φ : ℕ → E → EReal) (hnn : ∀ j x, 0 ≤ φ j x) (hφ0 : ∀ j, φ j 0 = 0)
    (hconv : ∀ j, ConvexPotential (φ j)) (hφ : ∀ j, PotentialIntegrable (φ j) μ)
    (b : ℝ) (hlower : ∀ᶠ j in atTop, (b : EReal) ≤ variationalFunctional dx μ (φ j)) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ j, (∫ x, (φ j x).toReal ∂μ) ≤ B) ∧
      (⨆ j, ∫⁻ x, (φ j x).toENNReal ∂μ) ≠ ⊤ := by sorry
