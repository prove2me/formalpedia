-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_limsup_density_legendre_le_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:38.226033+00:00
-- url     : https://prove2.me/theorems/17296063-1b71-41d2-bce0-7da325d4cf6f
-- title:
--   Pointwise Limsup Bound For Legendre Densities
-- statement:
--   This is the pointwise density component of the upper semicontinuity statement associated with Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as a partial formalization.
--
--   Let $E$ be a real-inner-product normed additive group, let $\phi_j:E\to\overline{\mathbb R}$, let $\psi:E\to\overline{\mathbb R}$, and let $K\subseteq E$. Assume:
--
--   1. For every $x\in K$, $\phi_j(x)\to\psi(x)$.
--   2. For every $y\in E$,
--      $$\psi^*(y)=\sup_{x\in K}\bigl(\langle x,y\rangle-\psi(x)\bigr).$$
--
--   Then, for every $y\in E$,
--   $$\limsup_{j\to\infty}\operatorname{density}(\phi_j^*)(y)\le\operatorname{density}(\psi^*)(y).$$
--
--   The result allows extended-real conjugate values and density values in $[0,\infty]$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L66-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le_408915f
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hsup : ∀ y, legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x)
    (y : E) :
    limsup (fun j => density (legendre (φ j)) y) atTop ≤ density (legendre ψ) y := by sorry
