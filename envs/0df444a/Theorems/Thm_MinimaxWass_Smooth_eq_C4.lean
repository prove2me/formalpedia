-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_eq_C4
-- name    : MinimaxWass.Smooth.eq_C4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:58.672689+00:00
-- url     : https://prove2.me/theorems/470cf107-ad04-408a-bc0c-6b167547e071
-- title:
--   (C.4), pp. 16–17 — w.p. ≥ 1 − δ/2, R_{ϱ,p}(P, f̂) − R_{ϱ,p}(P_n, f̂) ≤ 2ℜ_n(Φ) + M√(2log(2/δ)/n)
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space, $p\ge1$, $\varrho>0$, $\mathcal F$ a class of upper semicontinuous functions with $0\le f\le M$ and finite entropy integral $\mathfrak C(\mathcal F)<\infty$, and suppose Assumption 4 holds with constants $C_0\ge0$, $z_0$. Let $Z_1,\dots,Z_n$ ($n>0$) be i.i.d. from a Borel probability measure $P$, let $\hat f$ be a local minimax ERM (7), and let $\Lambda$, $\Phi$ be as in Appendix C.5 and $\mathfrak R_n(\Phi)$ the expected Rademacher average of $\Phi$. For every $\delta\in(0,1)$, with probability at least $1-\delta/2$,
--
--   $$R_{\varrho,p}(P,\hat f)-R_{\varrho,p}(P_n,\hat f)\le2\,\mathfrak R_n(\Phi)+M\sqrt{\frac{2\log(2/\delta)}{n}}.$$
--
--   This is the uniform deviation bound for the ERM's own local worst-case risk, the first of the two probabilistic ingredients of Theorem 3.
--
--   **Formalization Note** "With probability at least $1-\delta/2$" is stated as: the outer $P^{\otimes n}$-measure of the set of samples where the inequality fails is at most $\delta/2$. This equals the paper's probability when that set is measurable and is stronger otherwise; no measurability of $\hat f$ is assumed. The hypothesis $\mathfrak C(\mathcal F)<\infty$ (the bound of Theorem 3 is vacuous otherwise) makes $\mathcal F$ totally bounded in the uniform norm, so the supremum inside $\mathfrak R_n(\Phi)$ is a measurable bounded function of the sample.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, pp. 16–17, Appendix C.5 (proof of Theorem 3), (C.4)

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- (C.4), pp. 16–17: with probability at least `1 − δ/2`,
`R_{ϱ,p}(P, f̂) − R_{ϱ,p}(P_n, f̂) ≤ 2 ℜ_n(Φ) + M √(2 log(2/δ)/n)`. -/
theorem eq_C4 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbdd : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    {ℱ : Set (𝒵 → ℝ)} {M : ℝ}
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f) (hbddF : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    {f₀ : 𝒵 → ℝ} (hf₀ : f₀ ∈ ℱ) {z₀ : 𝒵} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hf₀_le : ∀ z, f₀ z ≤ C₀ * dist z z₀ ^ p)
    (hC : MinimaxWass.DataDep.entropyIntegral ℱ < ⊤)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n)
    (fhat : (Fin n → 𝒵) → 𝒵 → ℝ) (hfhat_mem : ∀ ω, fhat ω ∈ ℱ)
    (hfhat_min : ∀ ω, ∀ f ∈ ℱ,
      MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) ≤ MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) f)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    sampleLaw P n {ω | MinimaxWass.DataDep.localRisk p ϱ P (fhat ω) - MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) >
        2 * MinimaxWass.Lipschitz.rademacherAvg P n (phiClass p (lamInterval 𝒵 p ϱ C₀) ℱ) +
          M * Real.sqrt (2 * Real.log (2 / δ) / n)} ≤ ENNReal.ofReal (δ / 2) := by sorry

end MinimaxWass.Smooth
