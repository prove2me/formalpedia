-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_normalized_maximizing_sequence_408915f
-- name    : FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:45.902827+00:00
-- url     : https://prove2.me/theorems/393cf48e-177e-4322-81a1-7942e1ae9779
-- title:
--   Normalized Maximizing Sequence For The Variational Functional
-- statement:
--   This formalizes a partial compactness consequence related to Proposition 12 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as a stronger paper statement.
--
--   Let $E$ be finite-dimensional with additive Haar measure $dx$, and let $\mu$ be a probability measure satisfying:
--
--   1. Every linear subspace with full $\mu$-measure is all of $E$.
--   2. The identity map is $\mu$-integrable.
--   3. $\int x\,d\mu(x)=0$.
--
--   Then there exist $S\in\mathbb R$ and a sequence $\phi_j:E\to\overline{\mathbb R}$ such that, for every $j$, `ConvexPotential (φ j)`, `PotentialIntegrable (φ j) μ`, $\phi_j\ge0$, and $\phi_j(0)=0$. Moreover,
--   $$\operatorname{variationalFunctional}(dx,\mu,\phi_j)\longrightarrow(S:\overline{\mathbb R})$$
--   as $j\to\infty$, and every nonnegative normalized convex potential $\psi$ with `PotentialIntegrable ψ μ` satisfies
--   $$\operatorname{variationalFunctional}(dx,\mu,\psi)\le(S:\overline{\mathbb R}).$$
--
--   This provides a normalized maximizing sequence and an upper-bound value, but does not assert mass convergence or attainment by a single potential.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L32-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.VariationalMaximum`, declaration `FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence_408915f (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (φ : ℕ → E → EReal),
      (∀ j, ConvexPotential (φ j)) ∧ (∀ j, PotentialIntegrable (φ j) μ) ∧
      (∀ j x, 0 ≤ φ j x) ∧ (∀ j, φ j 0 = 0) ∧
      Tendsto (fun j => variationalFunctional dx μ (φ j)) atTop (𝓝 (S : EReal)) ∧
      ∀ ψ : E → EReal, ConvexPotential ψ → PotentialIntegrable ψ μ →
        (∀ x, 0 ≤ ψ x) → ψ 0 = 0 → variationalFunctional dx μ ψ ≤ (S : EReal) := by sorry
