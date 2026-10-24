-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_limsup_mass_legendre_le_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:21.937952+00:00
-- url     : https://prove2.me/theorems/d6f7c96d-fa31-440b-8259-8cbc996792d7
-- title:
--   Upper Semicontinuity Of Legendre Conjugate Mass
-- statement:
--   This formalizes Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited as “Compactness of normalised potentials,” in a partial form.
--
--   Let $E$ be finite-dimensional with an additive Haar measure $dx$. Let $\phi_j,\psi:E\to\overline{\mathbb R}$ and let $K\subseteq E$ be open and convex with $0\in K$. Assume:
--
--   1. $\psi$ is finite-valued in the extended-real sense on $K$.
--   2. $\phi_j(x)\to\psi(x)$ for every $x\in K$.
--   3. $\psi(tx)\to\psi(x)$ as $t\to1$ from below for every $x$.
--   4. $\psi(x)=+\infty$ whenever $x\notin\overline K$.
--
--   Then
--   $$\operatorname{mass}(dx,\psi^*)\ne+\infty$$
--   and
--   $$\limsup_{j\to\infty}\operatorname{mass}(dx,\phi_j^*)\le\operatorname{mass}(dx,\psi^*).$$
--
--   No finiteness of the individual source masses is assumed, and the conclusion permits zero mass.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Lemma 17. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L153-L185 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le`; the repository is private at upload time).

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

theorem FunctionalInequalities.Probability.MomentMeasure.limsup_mass_legendre_le_408915f
    (dx : Measure E) [dx.IsAddHaarMeasure]
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (hfin : ∀ x ∈ K, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) :
    mass dx (legendre ψ) ≠ ⊤ ∧
      limsup (fun j => mass dx (legendre (φ j))) atTop ≤ mass dx (legendre ψ) := by sorry
