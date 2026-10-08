-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_lemma_5
-- name    : MinimaxWass.Smooth.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:44.373991+00:00
-- url     : https://prove2.me/theorems/dc7a08d0-de76-4aff-82f6-f0c5ca1b21cc
-- title:
--   Lemma 5, p. 19 — ℜ_n(Φ) ≤ (24/√n)𝔆(ℱ) + (12C₀(2 diam(𝒵))^p/√n)(1 + (diam(𝒵)/ϱ)^p)
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space, $p\ge1$, $\varrho>0$, $C_0\ge0$, and $\mathcal F$ a class of upper semicontinuous functions with $0\le f\le M$ and finite entropy integral $\mathfrak C(\mathcal F)$. Let
--
--   $$\Lambda=\Bigl[0,\;C_0 2^{p-1}\Bigl(1+\Bigl(\tfrac{\mathrm{diam}(\mathcal Z)}{\varrho}\Bigr)^p\Bigr)\Bigr],\qquad \Phi=\{\varphi_{\lambda,f}:\lambda\in\Lambda,\ f\in\mathcal F\},$$
--
--   let $P$ be a Borel probability measure and $n>0$. The expected Rademacher average of $\Phi$ under i.i.d. samples from $P$ satisfies
--
--   $$\mathfrak R_n(\Phi)\le\frac{24}{\sqrt n}\,\mathfrak C(\mathcal F)+\frac{12\,C_0\,(2\,\mathrm{diam}(\mathcal Z))^p}{\sqrt n}\Bigl(1+\Bigl(\frac{\mathrm{diam}(\mathcal Z)}{\varrho}\Bigr)^p\Bigr).$$
--
--   The lemma bounds the complexity of the dual class by that of the hypothesis class plus a term for the one-dimensional multiplier, which is what turns (C.4) into the explicit rate of Theorem 3.
--
--   **Formalization Note** $\mathfrak C(\mathcal F)$ is valued in $[0,\infty]$; the hypothesis $\mathfrak C(\mathcal F)<\infty$ lets it enter the bound as a real number (when it is infinite the paper's bound is $+\infty$ and says nothing). The covering number in $\mathfrak C(\mathcal F)$ is the internal one. Assumption 4 is not needed: $C_0$ enters only through $\Lambda$.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 19, Appendix D, Lemma 5; proof pp. 19–20; Λ, Φ from Appendix C.5, p. 16

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- Lemma 5, p. 19: `ℜ_n(Φ) ≤ (24/√n) 𝔆(ℱ) + (12 C₀ (2 diam(𝒵))^p/√n)(1 + (diam(𝒵)/ϱ)^p)`. -/
theorem lemma_5 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbdd : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    {ℱ : Set (𝒵 → ℝ)} {M : ℝ}
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f) (hbddF : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hC : MinimaxWass.DataDep.entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n) :
    MinimaxWass.Lipschitz.rademacherAvg P n (phiClass p (lamInterval 𝒵 p ϱ C₀) ℱ) ≤
      24 / Real.sqrt n * (MinimaxWass.DataDep.entropyIntegral ℱ).toReal +
        12 * C₀ * (2 * Metric.diam (Set.univ : Set 𝒵)) ^ p / Real.sqrt n *
          (1 + (Metric.diam (Set.univ : Set 𝒵) / ϱ) ^ p) := by sorry

end MinimaxWass.Smooth
