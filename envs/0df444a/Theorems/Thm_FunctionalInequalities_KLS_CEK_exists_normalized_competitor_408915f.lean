-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_normalized_competitor_408915f
-- name    : FunctionalInequalities.KLS.CEK.exists_normalized_competitor_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:36.482466+00:00
-- url     : https://prove2.me/theorems/6a5c2f8f-54e8-48e2-b86c-4a22e37eb8bf
-- title:
--   Existence of an Epsilon-Normalized Convex Competitor
-- statement:
--   This formalizes the reduction step in the proof of Proposition 12 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $dx$ be an additive Haar measure and let $\mu$ be a probability measure on a finite-dimensional real inner-product space. Assume:
--
--   1. $\mu$ is not concentrated on any proper linear subspace;
--   2. the identity map is $\mu$-integrable;
--   3. $\mu$ is centered, $\int x\,d\mu(x)=0$;
--   4. $f$ is potential-integrable;
--   5. $\varepsilon>0$.
--
--   Then there exists $\psi:E\to\overline{\mathbb R}$ such that $\psi$ is a convex potential, is potential-integrable, and
--
--   $$
--   \psi(x)\geq0,\qquad \psi(0)=0,
--   $$
--
--   and its variational value satisfies
--
--   $$
--   \mathcal V_{dx,\mu}(f)
--   \leq
--   \mathcal V_{dx,\mu}(\psi)+\varepsilon.
--   $$
--
--   This provides an epsilon-close normalized convex competitor for variational arguments.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/Competitors.lean#L29-L54 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.Competitors`, declaration `FunctionalInequalities.KLS.CEK.exists_normalized_competitor`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.CEK.exists_normalized_competitor_408915f (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (f : E → EReal) (hf : PotentialIntegrable f μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : E → EReal, ConvexPotential ψ ∧ PotentialIntegrable ψ μ ∧
      (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      variationalFunctional dx μ f ≤ variationalFunctional dx μ ψ + (ε : EReal) := by sorry
