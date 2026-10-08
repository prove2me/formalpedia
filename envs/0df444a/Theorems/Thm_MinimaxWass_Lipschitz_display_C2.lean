-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_display_C2
-- name    : MinimaxWass.Lipschitz.display_C2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:55.991802+00:00
-- url     : https://prove2.me/theorems/85cc6450-40a4-4968-abae-558806d635f8
-- title:
--   Appendix C.5, (C.2), p. 16 — for an achiever f* and its dual minimiser λ*, R_{ϱ,p}(P_n, f*) − R_{ϱ,p}(P, f*) ≤ ∫ φ_{λ*,f*} d(P_n − P)
-- statement:
--   Let $\mathcal Z$ be a bounded Polish space, $p \ge 1$, $\varrho > 0$, and $\mathcal F$ a class of upper semicontinuous functions with $0 \le f \le M$. Let $P$ be a probability measure on $\mathcal Z$, let $f^* \in \mathcal F$ be an achiever of the local minimax risk, $R_{\varrho,p}(P,f^*) = R^*_{\varrho,p}(P,\mathcal F)$, and let $\lambda^* \ge 0$ minimize $\lambda \mapsto \lambda\varrho^p + \mathbf E_P[\varphi_{\lambda,f^*}(Z)]$ over $\lambda \ge 0$. Then for every sample $Z_1,\dots,Z_n$ ($n \ge 1$) with empirical distribution $P_n$,
--
--   $$R_{\varrho,p}(P_n,f^*) - R_{\varrho,p}(P,f^*) \le \frac1n\sum_{i=1}^n \varphi_{\lambda^*,f^*}(Z_i) - \int_{\mathcal Z}\varphi_{\lambda^*,f^*}(z)\,P(dz).$$
--
--   This deterministic inequality reduces the deviation of the local worst-case risk of the fixed hypothesis $f^*$ to the deviation of an empirical mean of one bounded function, which Hoeffding's inequality then controls (C.5).
--
--   **Formalization Note** The integral against $P_n - P$ is written as the empirical average minus the $P$-integral. The achiever $f^*$ is a hypothesis, as printed.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 16, Appendix C.5 (proof of Theorem 3), display (C.2); used for Theorem 2 per Appendix C.3, p. 15

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem display_C2 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF_usc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hF_bdd : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (P : ProbabilityMeasure 𝒵)
    (fstar : 𝒵 → ℝ) (hfstar_mem : fstar ∈ ℱ)
    (hfstar_min : ∀ f ∈ ℱ, MinimaxWass.DataDep.localRisk p ϱ P fstar ≤ MinimaxWass.DataDep.localRisk p ϱ P f)
    (lamstar : ℝ) (hlamstar_nonneg : 0 ≤ lamstar)
    (hlamstar_min : ∀ lam : ℝ, 0 ≤ lam →
      lamstar * ϱ ^ p + ∫ z, MinimaxWass.DataDep.phi p lamstar fstar z ∂(P : Measure 𝒵) ≤
        lam * ϱ ^ p + ∫ z, MinimaxWass.DataDep.phi p lam fstar z ∂(P : Measure 𝒵))
    {n : ℕ} (hn : 0 < n) (ω : Fin n → 𝒵) :
    MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) fstar - MinimaxWass.DataDep.localRisk p ϱ P fstar ≤
      (1 / (n : ℝ)) * ∑ i, MinimaxWass.DataDep.phi p lamstar fstar (ω i) -
        ∫ z, MinimaxWass.DataDep.phi p lamstar fstar z ∂(P : Measure 𝒵) := by sorry

end MinimaxWass.Lipschitz
