-- Prove2me | Theorems.Thm_MinimaxWass_Smooth_eq_C5
-- name    : MinimaxWass.Smooth.eq_C5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:37.481+00:00
-- url     : https://prove2.me/theorems/a0a416f2-df7d-481f-8bf3-b1f0f06a7fc7
-- title:
--   (C.5), p. 17 — w.p. ≥ 1 − δ/2, R_{ϱ,p}(P_n, f*) − R_{ϱ,p}(P, f*) ≤ M√(log(2/δ)/(2n)) for an achiever f*
-- statement:
--   Let $\mathcal Z$ be a bounded Polish metric space, $p\ge1$, $\varrho>0$, and $\mathcal F$ a class of upper semicontinuous functions with $0\le f\le M$. Let $Z_1,\dots,Z_n$ ($n>0$) be i.i.d. from a Borel probability measure $P$, with empirical distribution $P_n$, and let $f^*\in\mathcal F$ be an achiever of the local minimax risk, $R_{\varrho,p}(P,f^*)=R^*_{\varrho,p}(P,\mathcal F)$. For every $\delta\in(0,1)$, with probability at least $1-\delta/2$,
--
--   $$R_{\varrho,p}(P_n,f^*)-R_{\varrho,p}(P,f^*)\le M\sqrt{\frac{\log(2/\delta)}{2n}}.$$
--
--   This is the second probabilistic ingredient of Theorem 3: the empirical local worst-case risk of the fixed comparator $f^*$ does not exceed its population value by much.
--
--   **Formalization Note** As in (C.4), the probability statement bounds the outer $P^{\otimes n}$-measure of the failure set by $\delta/2$. The achiever $f^*$ is a hypothesis, as on the page.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 17, Appendix C.5 (proof of Theorem 3), (C.5)

import Mathlib
import Definitions.Def_MinimaxWass_Smooth_Setting

open MeasureTheory
open scoped ENNReal NNReal

namespace MinimaxWass.Smooth

/-- (C.5), p. 17: for an achiever `f*` of `R*_{ϱ,p}(P, ℱ)`, with probability at least
`1 − δ/2`, `R_{ϱ,p}(P_n, f*) − R_{ϱ,p}(P, f*) ≤ M √(log(2/δ)/(2n))`. -/
theorem eq_C5 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵] [PolishSpace 𝒵]
    (hbdd : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    {ℱ : Set (𝒵 → ℝ)} {M : ℝ}
    (husc : ∀ f ∈ ℱ, UpperSemicontinuous f) (hbddF : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (P : ProbabilityMeasure 𝒵) {n : ℕ} (hn : 0 < n)
    {fstar : 𝒵 → ℝ} (hfstar_mem : fstar ∈ ℱ)
    (hfstar_ach : MinimaxWass.DataDep.localRisk p ϱ P fstar = MinimaxWass.Lipschitz.localMinimaxRisk p ϱ P ℱ)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    sampleLaw P n {ω | MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) fstar - MinimaxWass.DataDep.localRisk p ϱ P fstar >
        M * Real.sqrt (Real.log (2 / δ) / (2 * n))} ≤ ENNReal.ofReal (δ / 2) := by sorry

end MinimaxWass.Smooth
