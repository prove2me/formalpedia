-- Prove2me | Theorems.Thm_MinimaxATE_Learnability_lemma_5_5
-- name    : MinimaxATE.Learnability.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:00:18.58507+00:00
-- url     : https://prove2.me/theorems/e08544c1-f393-4c97-9602-56e7322ad7c9
-- title:
--   Lemma 5.5 — a signed measure on $[u,L^2u]$ with total mass $\le1$, first moment $u/A$ ($A<4$) and vanishing moments of degrees $2,\dots,L$
-- statement:
--   Let $u>0$, let $L\ge2$ be an integer and set $\lambda=L^2u$. There is a discrete signed measure $\xi=\sum_{j=1}^L w_j\delta_{q_j}$ with locations $q_1,\dots,q_L\in[u,\lambda]$ and real weights $w_1,\dots,w_L$ such that, for some $A<4$,
--   $$\sum_{j=1}^L|w_j|\le1,\qquad\sum_{j=1}^Lq_j|w_j|=u,\qquad\sum_{j=1}^Lq_jw_j=\frac uA,\qquad\sum_{j=1}^Lq_j^h w_j=0\quad\text{for all }h\in\{2,\dots,L\}.$$
--
--   This is the moment-matching device behind the lower bound: it lets two priors agree on all moments of degree $2$ to $L$ while their first moments differ.
--
--   **Formalization Note.** Locations and weights are indexed by `Fin L`; the locations need not be distinct.
--
--   Differences from the source:
--   - encoding: "for some A < 4" with u/A → ∃ A with A ≠ 0 and A < 4; reason: u/A is undefined at A = 0 (Lean's u/0 = 0 would otherwise let a degenerate measure pass).
-- source:
--   Cai, Kalavasis, Mamali, Mehrotra, Zampetakis, Minimax Rates for Estimation of Average Treatment Effects in Observational Studies, STOC 2027 submission (manuscript sha256 89998c39…), p. 36 (PDF 38), Lemma 5.5; proof p. 38-39 (PDF 40-41)

import Mathlib

namespace MinimaxATE.Learnability

theorem lemma_5_5 (u : ℝ) (hu : 0 < u) (L : ℕ) (hL : 2 ≤ L) :
    ∃ (q w : Fin L → ℝ) (A : ℝ), A ≠ 0 ∧ A < 4 ∧
      (∀ j, q j ∈ Set.Icc u ((L : ℝ) ^ 2 * u)) ∧
      ∑ j, |w j| ≤ 1 ∧
      ∑ j, q j * |w j| = u ∧
      ∑ j, q j * w j = u / A ∧
      ∀ h : ℕ, 2 ≤ h → h ≤ L → ∑ j, q j ^ h * w j = 0 := by sorry

end MinimaxATE.Learnability
