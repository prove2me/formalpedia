-- Prove2me | Theorems.Thm_MinimaxWass_Lipschitz_display_C5
-- name    : MinimaxWass.Lipschitz.display_C5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:51.309398+00:00
-- url     : https://prove2.me/theorems/f9e0275d-95ec-40a7-890f-879a98477969
-- title:
--   Appendix C.5, (C.5), p. 17 — w.p. ≥ 1 − δ/2, R_{ϱ,p}(P_n, f*) − R_{ϱ,p}(P, f*) ≤ M√(log(2/δ)/(2n)) for an achiever f*
-- statement:
--   Let $\mathcal Z$ be a bounded Polish space, $p \ge 1$, $\varrho > 0$, and $\mathcal F$ a class of upper semicontinuous functions with $0 \le f \le M$ (Assumptions 1–2). Let $Z_1,\dots,Z_n$ ($n \ge 1$) be i.i.d. from $P$ with empirical distribution $P_n$, let $f^* \in \mathcal F$ be an achiever of the local minimax risk $R^*_{\varrho,p}(P,\mathcal F)$, and let $0 < \delta < 1$. Then with probability at least $1 - \delta/2$,
--
--   $$R_{\varrho,p}(P_n,f^*) - R_{\varrho,p}(P,f^*) \le M\sqrt{\frac{\log(2/\delta)}{2n}}.$$
--
--   Together with (C.4) this bounds both halves of the excess-risk decomposition behind Theorem 2.
--
--   **Formalization Note** "With probability at least $1-\delta/2$" is read through the outer measure under $P^{\otimes n}$ of the failure set, as in (C.4). The achiever $f^*$ is a hypothesis, as printed.
-- source:
--   Lee & Raginsky, Minimax statistical learning with Wasserstein distances, arXiv:1705.07815v2, p. 17, Appendix C.5, display (C.5); used for Theorem 2 per Appendix C.3, p. 15

import Mathlib
import Definitions.Def_MinimaxWass_Lipschitz_Setting

open MeasureTheory WassersteinLinOpt.Ball
open scoped ENNReal NNReal

namespace MinimaxWass.Lipschitz

theorem display_C5 {𝒵 : Type*} [MetricSpace 𝒵] [MeasurableSpace 𝒵] [BorelSpace 𝒵]
    [PolishSpace 𝒵] (hZ : Bornology.IsBounded (Set.univ : Set 𝒵))
    {p ϱ M : ℝ} (hp : 1 ≤ p) (hϱ : 0 < ϱ)
    (ℱ : Set (𝒵 → ℝ)) (hF_usc : ∀ f ∈ ℱ, UpperSemicontinuous f)
    (hF_bdd : ∀ f ∈ ℱ, ∀ z, 0 ≤ f z ∧ f z ≤ M)
    (P : ProbabilityMeasure 𝒵)
    (fstar : 𝒵 → ℝ) (hfstar_mem : fstar ∈ ℱ)
    (hfstar_min : ∀ f ∈ ℱ, MinimaxWass.DataDep.localRisk p ϱ P fstar ≤ MinimaxWass.DataDep.localRisk p ϱ P f)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {n : ℕ} (hn : 0 < n) :
    Measure.pi (fun _ : Fin n => (P : Measure 𝒵))
        {ω | MinimaxWass.DataDep.localRisk p ϱ (empiricalPM hn ω) fstar - MinimaxWass.DataDep.localRisk p ϱ P fstar >
          M * Real.sqrt (Real.log (2 / δ) / (2 * n))} ≤
      ENNReal.ofReal (δ / 2) := by sorry

end MinimaxWass.Lipschitz
