-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_eq_C3
-- name    : MinimaxWass.Smooth.eq_C3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:55.677044+00:00
-- url     : https://prove2.me/theorems/826e56e0-b1d7-439c-9441-518d4e7e9285
-- title:
--   (C.3), p. 16 — R_{ϱ,p}(P, f̂) − R_{ϱ,p}(P_n, f̂) ≤ sup_{φ∈Φ} ∫ φ d(P − P_n) for the local minimax ERM f̂
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space, $p\ge1$, $\varrho>0$, $\mathcal F$ a class of upper semicontinuous functions with $0\le f\le M$, and suppose Assumption 4 holds: some $f_0\in\mathcal F$ satisfies $f_0(z)\le C_0\,d^p_{\mathcal Z}(z,z_0)$ for all $z$, with $C_0\ge0$ and $z_0\in\mathcal Z$. Let $P$ be a Borel probability measure, $n>0$, and let $\hat f$ be a local minimax ERM: for every sample $\omega=(Z_1,\dots,Z_n)$, $\hat f(\omega)\in\mathcal F$ minimises $R_{\varrho,p}(P_n,\cdot)$ over $\mathcal F$. With
--
--   $$\Lambda=\Bigl[0,\;C_0 2^{p-1}\Bigl(1+\Bigl(\tfrac{\mathrm{diam}(\mathcal Z)}{\varrho}\Bigr)^p\Bigr)\Bigr],\qquad \Phi=\{\varphi_{\lambda,f}:\lambda\in\Lambda,\ f\in\mathcal F\},$$
--
--   for every sample
--
--   $$R_{\varrho,p}(P,\hat f)-R_{\varrho,p}(P_n,\hat f)\le\sup_{\varphi\in\Phi}\Bigl[\int_{\mathcal Z}\varphi\,dP-\frac1n\sum_{i=1}^n\varphi(Z_i)\Bigr].$$
--
--   The inequality replaces the data-dependent hypothesis $\hat f$ and its data-dependent dual multiplier by a supremum over a fixed function class, to which empirical-process bounds apply.
--
--   **Formalization Note** The ERM (7) is a sample-indexed selection $\hat f$ with membership and minimality hypotheses, not a choice function; these hypotheses can be met only when an empirical minimiser exists, which (7) presupposes. The integral against $P_n$ is the sample average.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 16, Appendix C.5 (proof of Theorem 3), (C.3); ERM (7), p. 4

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- (C.3), p. 16: for the local minimax ERM `f̂` and every sample,
`R_{ϱ,p}(P, f̂) − R_{ϱ,p}(P_n, f̂) ≤ sup_{φ ∈ Φ} ∫ φ d(P − P_n)`. -/
theorem eq_C3 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbdd : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    {ℱ : Set (𝒵 → ℝ)} {M : ℝ}
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f) (hbddF : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    {f₀ : 𝒵 → ℝ} (hf₀ : f₀ ∈ ℱ) {z₀ : 𝒵} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hf₀_le : ∀ z, f₀ z ≤ C₀ * dist z z₀ ^ p)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n)
    (fhat : (Fin n → 𝒵) → 𝒵 → ℝ) (hfhat_mem : ∀ ω, fhat ω ∈ ℱ)
    (hfhat_min : ∀ ω, ∀ f ∈ ℱ,
      MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) ≤ MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) f)
    (ω : Fin n → 𝒵) :
    MinimaxWass.DataDep.localRisk p ϱ P (fhat ω) - MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) ≤
      ⨆ g : phiClass p (lamInterval 𝒵 p ϱ C₀) ℱ,
        (∫ z, (g : 𝒵 → ℝ) z ∂(P : Measure 𝒵) - (1 / (n : ℝ)) * ∑ i, (g : 𝒵 → ℝ) (ω i)) := by sorry

end MinimaxWass.Smooth
