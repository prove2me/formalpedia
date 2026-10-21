-- Prove2me | Theorems.Thm_MCTSBandit_NonstatUCB_lemma_2
-- name    : MCTSBandit.NonstatUCB.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:50.924981+00:00
-- url     : https://prove2.me/theorems/82b196d9-9954-45cb-9ed7-59f4043d67dd
-- title:
--   Lemma 2 — expected pulls of a suboptimal arm
-- statement:
--   For a suboptimal arm $i\ne i_*$ with gap $\Delta_i=\mu_*-\mu_i$, the polynomial-bonus UCB run satisfies
--
--   $$\mathbb E[T_i(n)]\le\left(\frac{2}{\Delta_i}\beta^{1/\xi}\right)^{1/(1-\eta)}n^{\alpha/(\xi(1-\eta))}+\frac{2}{\alpha-2}+1.$$
--
--   This bounds the expected number of plays of each arm below the limiting optimum, yielding the convergence part of Theorem 3.
--
--   **Formalization Note** The run's arm-selection events are measurable so the expectation is defined by a genuine bounded integral.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, p. 17, Lemma 2

import Definitions.Def_MCTSBandit_NonstatUCB_UCB

open MeasureTheory

namespace MCTSBandit.NonstatUCB

universe u

/-- Shah–Xie–Xu, Lemma 2, p. 17. -/
theorem lemma_2 {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (istar i : Fin K)
    (I : ℕ → Ω → Fin K) (R β ξ η α : ℝ)
    (hR : 0 < R) (hβ : 1 < β) (hξ : 0 < ξ)
    (hη0 : (1 / 2 : ℝ) ≤ η) (hη1 : η < 1)
    (hα0 : ξ * η * (1 - η) ≤ α) (hα1 : α < ξ * (1 - η))
    (hα2 : 2 < α)
    (hM : IsNonstatMAB P X μ R β ξ η)
    (hopt : IsUniqueOpt μ istar) (hI : IsUCBRun X β ξ α η I)
    (hIm : RunMeasurable I) (hi : i ≠ istar) :
    ∀ n : ℕ,
      (∫ ω, (pullCount I i n ω : ℝ) ∂P) ≤
        ((2 / (μ istar - μ i)) * β ^ (1 / ξ)) ^ (1 / (1 - η)) *
          (n : ℝ) ^ (α / (ξ * (1 - η))) + 2 / (α - 2) + 1 := by sorry

end MCTSBandit.NonstatUCB
