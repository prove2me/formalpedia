-- Prove2me | Theorems.Thm_MCTSBandit_NonstatUCB_lemma_3
-- name    : MCTSBandit.NonstatUCB.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:55.521984+00:00
-- url     : https://prove2.me/theorems/11368847-fd2d-4e94-a6c8-5a98693800e4
-- title:
--   Lemma 3 — two polynomial tails at the finite-sample scale
-- statement:
--   Let $n\ge N_p$, $x\ge1$, and $r_0=n^\eta+2R(K-1)(3+A(n))$, where $A(n)$ is (20) and $N_p$ is the first positive integer with $A(N_p)\le N_p$. Then both tails of cumulative reward obey
--
--   $$\mathbb P(n\bar X_n-n\mu_*\ge r_0x),\quad\mathbb P(n\bar X_n-n\mu_*\le-r_0x)\le\frac{\beta}{x^\xi}+\frac{2(K-1)}{(\alpha-1)((1+A(n))x)^{\alpha-1}}.$$
--
--   The lemma is the finite-sample concentration estimate refined to obtain Theorem 3.B.
--
--   **Formalization Note** The condition $n\ge N_p$ is represented by an earlier positive $t\le n$ with $A(t)\le t$; this avoids giving an empty minimum a default value.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, p. 19, Lemma 3; p. 18, (20)–(21)

import Definitions.Def_MCTSBandit_NonstatUCB_UCB

open MeasureTheory

namespace MCTSBandit.NonstatUCB

universe u

/-- Shah–Xie–Xu, Lemma 3, p. 19. -/
theorem lemma_3 {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (istar : Fin K)
    (I : ℕ → Ω → Fin K) (R β ξ η α Δ : ℝ)
    (hR : 0 < R) (hβ : 1 < β) (hξ : 0 < ξ)
    (hη0 : (1 / 2 : ℝ) ≤ η) (hη1 : η < 1)
    (hα0 : ξ * η * (1 - η) ≤ α) (hα1 : α < ξ * (1 - η))
    (hα2 : 2 < α)
    (hM : IsNonstatMAB P X μ R β ξ η)
    (hgap : GapLB μ istar Δ) (hI : IsUCBRun X β ξ α η I)
    (hIm : RunMeasurable I) :
    ∀ (n : ℕ) (x : ℝ),
      (∃ t : ℕ, 1 ≤ t ∧ t ≤ n ∧ Afun Δ β ξ α η t ≤ t) →
      1 ≤ x →
      let r0 : ℝ := (n : ℝ) ^ η +
        2 * R * ((K : ℝ) - 1) * (3 + Afun Δ β ξ α η n)
      (P {ω | r0 * x ≤ (n : ℝ) * runAvg X I n ω - (n : ℝ) * μ istar}
        ≤ ENNReal.ofReal
          (β / x ^ ξ +
            2 * ((K : ℝ) - 1) /
              ((α - 1) * ((1 + Afun Δ β ξ α η n) * x) ^ (α - 1)))) ∧
      (P {ω | (n : ℝ) * runAvg X I n ω - (n : ℝ) * μ istar ≤ -(r0 * x)}
        ≤ ENNReal.ofReal
          (β / x ^ ξ +
            2 * ((K : ℝ) - 1) /
              ((α - 1) * ((1 + Afun Δ β ξ α η n) * x) ^ (α - 1)))) := by sorry

end MCTSBandit.NonstatUCB
