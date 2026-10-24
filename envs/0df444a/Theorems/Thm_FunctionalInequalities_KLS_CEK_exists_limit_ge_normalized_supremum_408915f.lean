-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_limit_ge_normalized_supremum_408915f
-- name    : FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:26.925098+00:00
-- url     : https://prove2.me/theorems/690ba6a5-e855-4e2e-8b29-479a7cfee7fb
-- title:
--   Normalized Supremum Witness
-- statement:
--   This formalizes the variational-existence part of Proposition 12 of Cordero–Klartag (arXiv:1304.0630v1), in a limit-based form.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $dx$ be an additive Haar measure, and let $\mu$ be a probability measure. Assume:
--
--   1. Every linear subspace $V\subseteq E$ with $\mu(V^c)=0$ is all of $E$.
--   2. The identity map on $E$ is integrable with respect to $\mu$.
--   3. The barycenter vanishes: $\int x\,d\mu=0$.
--
--   Then there exist $S\in\mathbb{R}$ and a function $\psi:E\to\overline{\mathbb{R}}$ such that $\psi$ is a convex potential, is potential-integrable with respect to $\mu$, is nonnegative, and satisfies $\psi(0)=0$. Its conjugate mass is finite and strictly positive, and
--
--   $$
--   (S:\overline{\mathbb{R}})\le I_{dx,\mu}(\psi),
--   $$
--
--   where `variationalFunctional` is $I_{dx,\mu}$. Moreover, every competitor $\eta$ that is convex, potential-integrable, nonnegative, and satisfies $\eta(0)=0$ obeys
--
--   $$
--   I_{dx,\mu}(\eta)\le S.
--   $$
--
--   This statement supplies a normalized potential whose value reaches the supremum level up to the displayed lower bound and is used to obtain an actual variational maximizer.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean#L85-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.VariationalMaximum`, declaration `FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum_408915f (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirstMoment : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ (S : ℝ) (ψ : E → EReal), ConvexPotential ψ ∧ PotentialIntegrable ψ μ ∧
      (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧ 0 < mass dx (legendre ψ) ∧ mass dx (legendre ψ) ≠ ⊤ ∧
      (S : EReal) ≤ variationalFunctional dx μ ψ ∧
      ∀ η : E → EReal, ConvexPotential η → PotentialIntegrable η μ →
        (∀ x, 0 ≤ η x) → η 0 = 0 → variationalFunctional dx μ η ≤ (S : EReal) := by sorry
