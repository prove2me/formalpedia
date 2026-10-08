-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_eq_C2
-- name    : MinimaxWass.Smooth.eq_C2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:29.158223+00:00
-- url     : https://prove2.me/theorems/e23bc85a-870f-408d-8662-0a16374225e3
-- title:
--   (C.2), p. 16 — R_{ϱ,p}(P_n, f*) − R_{ϱ,p}(P, f*) ≤ ∫ φ_{λ*,f*} d(P_n − P) for an achiever f* and its dual minimiser λ*
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space, $p\ge1$, $\varrho>0$, and $\mathcal F$ a class of upper semicontinuous functions with $0\le f\le M$. Let $P$ be a Borel probability measure, $n>0$, and let $f^*\in\mathcal F$ be an achiever of the local minimax risk, $R_{\varrho,p}(P,f^*)=R^*_{\varrho,p}(P,\mathcal F)$. Let $\lambda^*\ge0$ minimise $\lambda\mapsto\lambda\varrho^p+\mathbf E_P[\varphi_{\lambda,f^*}(Z)]$ over $\lambda\ge0$. Then for every sample $Z_1,\dots,Z_n$, with empirical distribution $P_n$,
--
--   $$R_{\varrho,p}(P_n,f^*)-R_{\varrho,p}(P,f^*)\le\int_{\mathcal Z}\varphi_{\lambda^*,f^*}(z)\,(P_n-P)(dz)=\frac1n\sum_{i=1}^n\varphi_{\lambda^*,f^*}(Z_i)-\mathbf E_P[\varphi_{\lambda^*,f^*}(Z)].$$
--
--   This deterministic inequality reduces the deviation of the local worst-case risk of the fixed hypothesis $f^*$ to the deviation of a single bounded function, which is then controlled by Hoeffding's inequality in (C.5).
--
--   **Formalization Note** The achiever $f^*$ and the minimiser $\lambda^*$ (the paper's $\arg\min$) are hypotheses, as on the page. The integral against $P_n$ is written as the sample average.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 16, Appendix C.5 (proof of Theorem 3), (C.2)

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- (C.2), p. 16: for an achiever `f*` of `R*_{ϱ,p}(P, ℱ)` and a minimiser `λ*` of its
`P`-dual objective, `R_{ϱ,p}(P_n, f*) − R_{ϱ,p}(P, f*) ≤ ∫ φ_{λ*,f*} d(P_n − P)` for every
sample. -/
theorem eq_C2 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbdd : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    {ℱ : Set (𝒵 → ℝ)} {M : ℝ}
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f) (hbddF : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n)
    {fstar : 𝒵 → ℝ} (hfstar_mem : fstar ∈ ℱ)
    (hfstar_ach : MinimaxWass.DataDep.localRisk p ϱ P fstar = MinimaxWass.Lipschitz.localMinimaxRisk p ϱ P ℱ)
    {lamstar : ℝ} (hlamstar_nonneg : 0 ≤ lamstar)
    (hlamstar_min : ∀ lam : ℝ, 0 ≤ lam →
      dualObjective p ϱ P fstar lamstar ≤ dualObjective p ϱ P fstar lam)
    (ω : Fin n → 𝒵) :
    MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) fstar - MinimaxWass.DataDep.localRisk p ϱ P fstar ≤
      (1 / (n : ℝ)) * ∑ i, MinimaxWass.DataDep.phi p lamstar fstar (ω i) - ∫ z, MinimaxWass.DataDep.phi p lamstar fstar z ∂(P : Measure 𝒵) := by sorry

end MinimaxWass.Smooth
