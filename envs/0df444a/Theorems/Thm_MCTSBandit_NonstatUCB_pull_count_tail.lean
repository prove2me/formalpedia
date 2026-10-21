-- Prove2me | Theorems.Thm_MCTSBandit_NonstatUCB_pull_count_tail
-- name    : MCTSBandit.NonstatUCB.pull_count_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:56.421632+00:00
-- url     : https://prove2.me/theorems/62d6d9ba-98e0-47aa-a847-6ce308ca3466
-- title:
--   Equation (36) — polynomial tail of a suboptimal pull count
-- statement:
--   For a suboptimal arm $i$, every horizon $n$ and $x\ge1$ satisfy
--
--   $$\mathbb P\!\left(T_i(n)\ge(3+A(n))x\right)\le\frac{2((1+A(n))x)^{1-\alpha}}{\alpha-1}.$$
--
--   The bound controls the number of nonoptimal plays at the scale used in Lemma 3.
--
--   **Formalization Note** The play-count event compares a natural-valued count with a real threshold. The statement follows the printed inequality; the ceiling choice needed to justify the intermediate proof step is recorded in moderation notes.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, p. 24, proof of Lemma 3, (36)

import Definitions.Def_MCTSBandit_NonstatUCB_UCB

open MeasureTheory

namespace MCTSBandit.NonstatUCB

universe u

/-- Shah–Xie–Xu, inequality (36), p. 24. -/
theorem pull_count_tail {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (istar i : Fin K)
    (I : ℕ → Ω → Fin K) (R β ξ η α Δ : ℝ)
    (hR : 0 < R) (hβ : 1 < β) (hξ : 0 < ξ)
    (hη0 : (1 / 2 : ℝ) ≤ η) (hη1 : η < 1)
    (hα0 : ξ * η * (1 - η) ≤ α) (hα1 : α < ξ * (1 - η))
    (hα2 : 2 < α)
    (hM : IsNonstatMAB P X μ R β ξ η)
    (hgap : GapLB μ istar Δ) (hI : IsUCBRun X β ξ α η I)
    (hIm : RunMeasurable I) (hi : i ≠ istar) :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ x →
      P {ω | (3 + (Afun Δ β ξ α η n : ℝ)) * x ≤
        (pullCount I i n ω : ℝ)}
        ≤ ENNReal.ofReal
          (2 * ((1 + (Afun Δ β ξ α η n : ℝ)) * x) ^ (1 - α) / (α - 1)) := by sorry

end MCTSBandit.NonstatUCB
