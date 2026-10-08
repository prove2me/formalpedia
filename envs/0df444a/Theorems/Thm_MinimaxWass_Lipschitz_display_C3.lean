-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_display_C3
-- name    : MinimaxWass.Lipschitz.display_C3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:48.698361+00:00
-- url     : https://prove2.me/theorems/acb65109-f6d2-4869-923d-448cc6b7b234
-- title:
--   Appendix C.3 with (C.3), pp. 15–16 — R_{ϱ,p}(P, f̂) − R_{ϱ,p}(P_n, f̂) ≤ sup_{φ∈Φ} ∫ φ d(P − P_n), Φ built on Λ = [0, Lϱ^{−(p−1)}]
-- statement:
--   Let $\mathcal Z$ be a bounded Polish space, $p \ge 1$, $\varrho > 0$, and $\mathcal F$ a class of upper semicontinuous functions with $0 \le f \le M$ that are uniformly $L$-Lipschitz with $L \ge 0$ (Assumptions 1–3). Let $P$ be a probability measure on $\mathcal Z$ and $n \ge 1$. For each sample $\omega = (Z_1,\dots,Z_n)$ let $\hat f = \hat f(\omega) \in \mathcal F$ be a local minimax ERM, i.e. a minimizer over $\mathcal F$ of $R_{\varrho,p}(P_n,\cdot)$ (display (7)). With $\Lambda = [0, L\varrho^{-(p-1)}]$ and $\Phi = \{\varphi_{\lambda,f} : \lambda \in \Lambda, f \in \mathcal F\}$, for every sample
--
--   $$R_{\varrho,p}(P,\hat f) - R_{\varrho,p}(P_n,\hat f) \le \sup_{\varphi \in \Phi}\Big[\int_{\mathcal Z}\varphi\,dP - \frac1n\sum_{i=1}^n \varphi(Z_i)\Big].$$
--
--   The paper proves Theorem 2 by repeating the proof of Theorem 3 with Lemma 1 in place of Lemma 2 (Appendix C.3); this item is display (C.3) of that proof with the interval $\Lambda$ that Lemma 1 provides. It replaces a data-dependent hypothesis and multiplier by a supremum over a fixed class, to which empirical-process bounds apply.
--
--   **Formalization Note** The ERM is a sample-indexed selection $\hat f : \mathcal Z^n \to \mathcal F$ given with its minimality hypothesis; it can exist only when an empirical minimizer exists, which (7) presupposes. The integral against $P - P_n$ is the $P$-integral minus the empirical average. $L \ge 0$ is a disclosed pin.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 15, Appendix C.3 (proof of Theorem 2); p. 16, Appendix C.5, display (C.3), with Λ of Lemma 1 (p. 6)

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem display_C3 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M L : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF_usc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hF_bdd : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (hL : 0 ≤ L) (hF_lip : ∀ f ∈ ℱ, ∀ z z' : 𝒵, f z' - f z ≤ L * dist z' z)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n)
    (fhat : (Fin n → 𝒵) → (𝒵 → ℝ)) (hfhat_mem : ∀ ω, fhat ω ∈ ℱ)
    (hfhat_min : ∀ ω, ∀ f ∈ ℱ,
      MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) ≤ MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) f)
    (ω : Fin n → 𝒵) :
    MinimaxWass.DataDep.localRisk p ϱ P (fhat ω) - MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) (fhat ω) ≤
      ⨆ g : phiClass p ϱ L ℱ,
        (∫ z, (g : 𝒵 → ℝ) z ∂(P : Measure 𝒵) - (1 / (n : ℝ)) * ∑ i, (g : 𝒵 → ℝ) (ω i)) := by sorry

end MinimaxWass.Lipschitz
