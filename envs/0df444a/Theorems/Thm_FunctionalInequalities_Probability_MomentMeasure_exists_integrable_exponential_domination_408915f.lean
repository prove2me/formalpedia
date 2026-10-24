-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_integrable_exponential_domination_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:36.884927+00:00
-- url     : https://prove2.me/theorems/eea1e0e8-0a97-4bbc-9eb2-4145b551ca6b
-- title:
--   Common Exponential Domination Of Conjugate Densities
-- statement:
--   This is the common-dominator construction used for the upper semicontinuity result associated with Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as a partial formalization.
--
--   Let $E$ be finite-dimensional with an additive Haar measure $dx$. Let $\phi_j:E\to\overline{\mathbb R}$, $\psi:E\to\overline{\mathbb R}$, and let $K\subseteq E$ be open with $0\in K$. Assume:
--
--   1. For every $x\in K$, $\psi(x)$ is neither $+\infty$ nor $-\infty$.
--   2. For every $x\in K$, $\phi_j(x)\to\psi(x)$ as $j\to\infty$.
--
--   Then there exist $c,M\in\mathbb R$ and $N\in\mathbb N$ with $c>0$ such that
--   $$\int_E\operatorname{ENNReal.ofReal}\!\left(\exp(M-c\|y\|)\right)\,dx(y)\ne+\infty,$$
--   while, for every $y\in E$,
--   $$\operatorname{density}(\psi^*)(y)\le\operatorname{ENNReal.ofReal}\!\left(\exp(M-c\|y\|)\right),$$
--   and for every $j\ge N$ the same bound holds with $\psi$ replaced by $\phi_j$.
--
--   This supplies a single integrable exponential envelope for the limiting and eventually indexed conjugate densities.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L115-L151 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination`; the repository is private at upload time).

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
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Probability.MomentMeasure.exists_integrable_exponential_domination_408915f
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x))) :
    ∃ (c M : ℝ) (N : ℕ), 0 < c ∧
      (∫⁻ y, ENNReal.ofReal (Real.exp (M - c * ‖y‖)) ∂dx) ≠ ⊤ ∧
      (∀ y, density (legendre ψ) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖))) ∧
      ∀ j, N ≤ j → ∀ y,
        density (legendre (φ j)) y ≤ ENNReal.ofReal (Real.exp (M - c * ‖y‖)) := by sorry
