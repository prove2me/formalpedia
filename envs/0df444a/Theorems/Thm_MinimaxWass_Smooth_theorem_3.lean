-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_theorem_3
-- name    : MinimaxWass.Smooth.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:38.820884+00:00
-- url     : https://prove2.me/theorems/87387d3e-fbc6-453d-b4cc-fa2fab764ada
-- title:
--   Theorem 3, p. 7 — under Assumptions 1, 2, 4, w.p. ≥ 1 − δ the local minimax ERM has excess local minimax risk at most (11)
-- statement:
--   Let $\mathcal Z$ be a Polish space with metric $d_{\mathcal Z}$, let $p\ge1$ and $\varrho>0$, and let $Z_1,\dots,Z_n$ ($n>0$) be i.i.d. from a Borel probability measure $P$ on $\mathcal Z$, with empirical distribution $P_n$. Assume:
--
--   1. (Assumption 1) $\mathcal Z$ is bounded: $\mathrm{diam}(\mathcal Z)<\infty$;
--   2. (Assumption 2) every $f\in\mathcal F$ is upper semicontinuous with $0\le f(z)\le M$;
--   3. (Assumption 4) some $f_0\in\mathcal F$ satisfies $f_0(z)\le C_0\,d^p_{\mathcal Z}(z,z_0)$ for all $z$, for some $C_0\ge0$ and $z_0\in\mathcal Z$;
--   4. the entropy integral $\mathfrak C(\mathcal F)$ is finite.
--
--   Let $\hat f$ be a local minimax ERM, $\hat f\in\arg\min_{f\in\mathcal F}R_{\varrho,p}(P_n,f)$ for every sample (7). Then for every $\delta\in(0,1)$, with probability at least $1-\delta$,
--
--   $$R_{\varrho,p}(P,\hat f)-R^*_{\varrho,p}(P,\mathcal F)\le\frac{48\,\mathfrak C(\mathcal F)}{\sqrt n}+\frac{24\,C_0\,(2\,\mathrm{diam}(\mathcal Z))^p}{\sqrt n}\Bigl(1+\Bigl(\frac{\mathrm{diam}(\mathcal Z)}{\varrho}\Bigr)^p\Bigr)+3M\sqrt{\frac{\log(2/\delta)}{2n}}.$$
--
--   The theorem shows that minimising the empirical local worst-case risk learns at rate $1/\sqrt n$ in excess local minimax risk without any uniform smoothness of the class: a single hypothesis that grows at most like $d^p_{\mathcal Z}(\cdot,z_0)$ suffices, and the price is a term that decreases as the radius $\varrho$ grows.
--
--   **Formalization Note** "With probability at least $1-\delta$" is: the outer $P^{\otimes n}$-measure of the samples where the bound fails is at most $\delta$ (equal to the probability for a measurable failure set, stronger otherwise). The ERM is a sample-indexed selection with membership and minimality hypotheses; no measurability of $\hat f$ is assumed, and no achiever of $R^*_{\varrho,p}(P,\mathcal F)$ is assumed (the proof on p. 16 picks one; the theorem does not need it). $\mathfrak C(\mathcal F)<\infty$ is a disclosed hypothesis: otherwise the bound is $+\infty$, while its real conversion would be $0$. $\mathcal Z$ carries its Borel $\sigma$-algebra; real powers are of nonnegative bases.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 7, Theorem 3, (11); Assumptions 1–2 p. 5, Assumption 4 p. 6, ERM (7) p. 4; proof Appendix C.5, pp. 16–17

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- Theorem 3, p. 7, (11): under Assumptions 1, 2, 4, with probability at least `1 − δ` the local
minimax ERM `f̂` satisfies the excess-MinimaxWass.DataDep.risk bound (11). -/
theorem theorem_3 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
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
    sampleLaw P n {ω | MinimaxWass.DataDep.localRisk p ϱ P (fhat ω) - MinimaxWass.Lipschitz.localMinimaxRisk p ϱ P ℱ >
        48 * (MinimaxWass.DataDep.entropyIntegral ℱ).toReal / Real.sqrt n +
          24 * C₀ * (2 * Metric.diam (Set.univ : Set 𝒵)) ^ p / Real.sqrt n *
            (1 + (Metric.diam (Set.univ : Set 𝒵) / ϱ) ^ p) +
          3 * M * Real.sqrt (Real.log (2 / δ) / (2 * n))} ≤ ENNReal.ofReal δ := by sorry

end MinimaxWass.Smooth
