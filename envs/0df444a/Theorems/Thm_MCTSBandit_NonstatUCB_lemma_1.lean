-- Prove2me | Theorems.Thm_MCTSBandit_NonstatUCB_lemma_1
-- name    : MCTSBandit.NonstatUCB.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:03.240348+00:00
-- url     : https://prove2.me/theorems/19ccf29b-9528-41d6-9ebf-c4c663c8e4f8
-- title:
--   Lemma 1 — a sufficiently played suboptimal arm has a small upper tail
-- statement:
--   Let $i\ne i_*$ be a suboptimal arm, with gap $\Delta_i=\mu_*-\mu_i>0$. Define $A_i(t)$ by (18). For integers $t\ge1$ and $A_i(t)\le s\le t$,
--
--   $$\mathbb P(U_{i,s,t}>\mu_*)\le t^{-\alpha}.$$
--
--   The estimate controls a suboptimal arm's index after enough plays and feeds the pull-count bounds.
--
--   **Formalization Note** Time $t\ge1$ makes the page's number-of-steps convention explicit. No run or independence hypothesis is used.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, p. 17, Lemma 1 and (18)

import Definitions.Def_MCTSBandit_NonstatUCB_UCB

open MeasureTheory

namespace MCTSBandit.NonstatUCB

universe u

/-- Shah–Xie–Xu, Lemma 1, p. 17. -/
theorem lemma_1 {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (istar i : Fin K)
    (R β ξ η α : ℝ)
    (hR : 0 < R) (hβ : 1 < β) (hξ : 0 < ξ)
    (hη0 : (1 / 2 : ℝ) ≤ η) (hη1 : η < 1)
    (hα0 : ξ * η * (1 - η) ≤ α) (hα1 : α < ξ * (1 - η))
    (hα2 : 2 < α)
    (hM : IsNonstatMAB P X μ R β ξ η)
    (hopt : IsUniqueOpt μ istar) (hi : i ≠ istar) :
    ∀ (s t : ℕ), 1 ≤ t →
      Aidx (μ istar - μ i) β ξ α η t ≤ s → s ≤ t →
      P {ω | μ istar < ucb X β ξ α η i s t ω}
        ≤ ENNReal.ofReal ((t : ℝ) ^ (-α)) := by sorry

end MCTSBandit.NonstatUCB
