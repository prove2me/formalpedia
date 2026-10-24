-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_uniform_functional_upper_408915f
-- name    : FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:37.07909+00:00
-- url     : https://prove2.me/theorems/2d4db28b-5de1-4690-9d2d-bf90715a438b
-- title:
--   Uniform Upper Bound For Admissible CEK Competitors
-- statement:
--   This is the finite-range reduction statement from the proof of Proposition 12 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), although no paper item directly cites this declaration.
--
--   Let $E$ be finite-dimensional with an additive Haar measure $dx$, and let $\mu$ be a probability measure. Assume:
--
--   1. Every linear subspace with full $\mu$-measure equals $E$.
--   2. The identity map is $\mu$-integrable.
--   3. $\int x\,d\mu(x)=0$.
--
--   Then there exists $U\in\mathbb R$ such that every $f:E\to\overline{\mathbb R}$ with `PotentialIntegrable f μ` satisfies
--   $$\operatorname{variationalFunctional}(dx,\mu,f)\le(U:\overline{\mathbb R}).$$
--
--   No convexity, nonnegativity, normalization, or finiteness of the conjugate mass is required of the competitor beyond `PotentialIntegrable`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/Competitors.lean#L55-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.Competitors`, declaration `FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper`; the repository is private at upload time).

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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.CEK
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper_408915f (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ U : ℝ, ∀ f : E → EReal, PotentialIntegrable f μ →
      variationalFunctional dx μ f ≤ (U : EReal) := by sorry
