-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_theorem_2
-- name    : MinimaxWass.Lipschitz.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:13.763956+00:00
-- url     : https://prove2.me/theorems/f8f757d9-e46e-4f0e-a6f9-d102ca3ecf49
-- title:
--   Theorem 2 (10), p. 6 — under Assumptions 1–3, w.p. ≥ 1 − δ, R_{ϱ,p}(P, f̂) − R*_{ϱ,p}(P, ℱ) ≤ 48𝔆(ℱ)/√n + 48L·diam(𝒵)^p/(√n ϱ^{p−1}) + 3M√(log(2/δ)/(2n))
-- statement:
--   Let $\mathcal Z$ be a Polish space with metric $d_{\mathcal Z}$ and finite diameter $\operatorname{diam}(\mathcal Z)$ (Assumption 1), let $p \ge 1$ and $\varrho > 0$, and let $\mathcal F$ be a class of upper semicontinuous functions $f : \mathcal Z \to \mathbb R$ with $0 \le f \le M$ (Assumption 2) that are uniformly $L$-Lipschitz, $f(z') - f(z) \le L\,d_{\mathcal Z}(z',z)$ for all $f \in \mathcal F$ and $z,z'$, with $L \ge 0$ (Assumption 3). Assume the entropy integral $\mathfrak C(\mathcal F) = \int_0^\infty \sqrt{\log\mathcal N(\mathcal F,\|\cdot\|_\infty,u)}\,du$ is finite. Let $Z_1,\dots,Z_n$ ($n \ge 1$) be i.i.d. from a probability measure $P$ with empirical distribution $P_n$, and let $\hat f \in \mathcal F$ be a local minimax ERM, $\hat f \in \arg\min_{f \in \mathcal F} R_{\varrho,p}(P_n,f)$. Then for every $\delta \in (0,1)$, with probability at least $1-\delta$,
--
--   $$R_{\varrho,p}(P,\hat f) - R^*_{\varrho,p}(P,\mathcal F) \le \frac{48\,\mathfrak C(\mathcal F)}{\sqrt n} + \frac{48 L\cdot\operatorname{diam}(\mathcal Z)^p}{\sqrt n\cdot\varrho^{p-1}} + 3M\sqrt{\frac{\log(2/\delta)}{2n}}.$$
--
--   Here $R_{\varrho,p}(P,f)$ is the worst-case risk of $f$ over the $p$-Wasserstein ball of radius $\varrho$ around $P$, and $R^*_{\varrho,p}(P,\mathcal F)$ its infimum over $\mathcal F$. The theorem says that, for a uniformly Lipschitz class, the robust ERM computed from the data is nearly optimal for the robust risk at the unknown $P$, with an excess of order $1/\sqrt n$; at $p = 1$ the bound does not depend on $\varrho$.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the outer measure under $P^{\otimes n}$ of the set of samples where the inequality fails is at most $\delta$. The ERM is a sample-indexed selection with its minimality hypothesis; no achiever of $R^*_{\varrho,p}(P,\mathcal F)$ is assumed. $\mathfrak C(\mathcal F) < \infty$ is a disclosed pin (otherwise the bound is $+\infty$) and enters as a real number; the covering number is the internal one. $L \ge 0$ is a disclosed pin. $\operatorname{diam}(\mathcal Z)$ is the diameter of the whole space, and powers with real exponent are real powers of nonnegative bases.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 6, Theorem 2, display (10); Assumptions 1–3, p. 5; (7), p. 4; proof Appendix C.3, p. 15, via Appendix C.5, pp. 16–17

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem theorem_2 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M L : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF_usc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hF_bdd : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hL : 0 ≤ L) (hF_lip : ∀ f ∈ ℱ, ∀ z z' : 𝒵, f z' - f z ≤ L * dist z' z)
    (hC : MinimaxWass.DataDep.entropyIntegral ℱ < ⊤)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n)
    (fhat : (Fin n → 𝒵) → (𝒵 → ℝ)) (hfhat_mem : ∀ ω, fhat ω ∈ ℱ)
    (hfhat_min : ∀ ω, ∀ f ∈ ℱ,
      MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) ≤ MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) f) :
    Measure.pi (fun _ : Fin n => (P : Measure 𝒵))
        {ω | MinimaxWass.DataDep.localRisk p ϱ P (fhat ω) - localMinimaxRisk p ϱ P ℱ >
          48 * (MinimaxWass.DataDep.entropyIntegral ℱ).toReal / Real.sqrt n +
            48 * L * Metric.diam (Set.univ : Set 𝒵) ^ p / (Real.sqrt n * ϱ ^ (p - 1)) +
            3 * M * Real.sqrt (Real.log (2 / δ) / (2 * n))} ≤
      ENNReal.ofReal δ := by sorry

end MinimaxWass.Lipschitz
