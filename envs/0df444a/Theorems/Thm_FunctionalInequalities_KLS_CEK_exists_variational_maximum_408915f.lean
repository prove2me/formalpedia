-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_variational_maximum_408915f
-- name    : FunctionalInequalities.KLS.CEK.exists_variational_maximum_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:25.914526+00:00
-- url     : https://prove2.me/theorems/61ad80a6-7549-4de4-8683-b4cdcb00056c
-- title:
--   Existence of a Variational Maximizer
-- statement:
--   This formalizes Proposition 12, display (38), of Cordero–Klartag (arXiv:1304.0630v1).
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $dx$ be an additive Haar measure, and let $\mu$ be a probability measure. Assume:
--
--   1. If a linear subspace $V\subseteq E$ satisfies $\mu(V^c)=0$, then $V=E$.
--   2. The identity map is integrable under $\mu$.
--   3. The barycenter is zero: $\int x\,d\mu=0$.
--
--   Then there exists $\phi:E\to\overline{\mathbb{R}}$ such that $\phi$ is a convex lower-semicontinuous potential, is potential-integrable under $\mu$, and
--
--   $$
--   \operatorname{mass}_{dx}(\phi^*)=1.
--   $$
--
--   For every potential-integrable competitor $f:E\to\overline{\mathbb{R}}$,
--
--   $$
--   I_{dx,\mu}(f)\le I_{dx,\mu}(\phi),
--   $$
--
--   where $\phi^*$ is `legendre`, the mass is `mass`, and $I_{dx,\mu}$ is `variationalFunctional`. This is the formalized variational-attainment conclusion; it does not assert essential continuity, an Euler–Lagrange identity, or a moment-map formula.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L134-L212 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.VariationalMaximum`, declaration `FunctionalInequalities.KLS.CEK.exists_variational_maximum`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

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

theorem FunctionalInequalities.KLS.CEK.exists_variational_maximum_408915f (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ φ : E → EReal, ConvexPotential φ ∧ LowerSemicontinuous φ ∧ PotentialIntegrable φ μ ∧
      mass dx (legendre φ) = 1 ∧
      ∀ f : E → EReal, PotentialIntegrable f μ →
        variationalFunctional dx μ f ≤ variationalFunctional dx μ φ := by sorry
