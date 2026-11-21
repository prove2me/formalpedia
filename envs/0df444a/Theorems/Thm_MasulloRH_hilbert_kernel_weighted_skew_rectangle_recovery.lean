-- Prove2me | Theorems.Thm_MasulloRH_hilbert_kernel_weighted_skew_rectangle_recovery
-- name    : MasulloRH.hilbert_kernel_weighted_skew_rectangle_recovery
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:54:57.713582+00:00
-- url     : https://prove2.me/theorems/e2bdca15-5ce0-421b-8bd1-931f915590df
-- title:
--   Continuous indentation of Hilbert-factor kernels on countably many skew diagonals
-- statement:
--   Let $G$ be a second-countable locally compact Hausdorff abelian group with Haar measure $\mu$, and let $(U_k)$ be a $D'$ differentiation sequence. Let $a,b$ be locally Bochner integrable functions from $G$ to a complex Hilbert space. Suppose $K(u,v)=\langle a(u),b(v)\rangle$ for $(\mu\otimes\mu)$-almost every $(u,v)$. For any countable family of measurable nonsingular maps $\sigma_j:G\to G$, there is a single conull set of $x$ for which the following holds for every $j$ and every continuous complex multiplier $q$:
--   $$\frac{\int_{xU_k\times\sigma_j(x)U_\ell} q(u,v)K(u,v)\,d\mu(u)\,d\mu(v)}{\mu(U_k)\mu(U_\ell)}\longrightarrow q(x,\sigma_j(x))\langle a(x),b(\sigma_j(x))\rangle.$$
--   The indices $k,\ell$ tend to infinity independently. This result concerns each fixed kernel. It includes the diagonal and every countable collection of translates.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026, Appendix A.5.3–4 and sections 10.4.2–3 and 12.1. Builds on the fixed-operator Schmidt argument in mission comment 04fc82b0-7a9c-4711-b478-f70628b457fa and the bounded-average multiplier lemma cbb83452-e074-466f-aa6a-99fb9a9b4110. The Haar differentiation milestone is 98e5565a-8bc2-40f0-b91d-857aa86b65aa. New direct formalization includes Hilbert-valued differentiation, all countable nonsingular skew maps, and independent rectangle radii.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Metrizable.Urysohn
import Definitions.Def_MasulloGRH_DSequences
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set MeasureTheory Filter
open scoped Pointwise ENNReal
open MasulloGRH
open scoped Topology

theorem MasulloRH.hilbert_kernel_weighted_skew_rectangle_recovery
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    (μ : Measure G) [μ.IsHaarMeasure] (U : ℕ → Set G) (C : ℝ) (hU : IsDPrimeSequence μ U C)
    (a b : G → E) (ha : LocallyIntegrable a μ) (hb : LocallyIntegrable b μ)
    (K : G × G → ℂ) (hK : K =ᵐ[μ.prod μ] (fun z => inner ℂ (a z.1) (b z.2)))
    {J : Type*} [Countable J] (σ : J → G → G) (hσ : ∀ j, Measure.QuasiMeasurePreserving (σ j) μ μ) :
    ∀ᵐ x ∂μ, ∀ j, ∀ (q : G × G → ℂ), Continuous q → Tendsto
      (fun kl : ℕ × ℕ => (((μ (U kl.1)).toReal)⁻¹ * ((μ (U kl.2)).toReal)⁻¹) •
        ∫ z in (x • U kl.1) ×ˢ ((σ j x) • U kl.2), q z * K z ∂μ.prod μ)
      atTop (𝓝 (q (x, σ j x) * inner ℂ (a x) (b (σ j x)))) := by sorry
