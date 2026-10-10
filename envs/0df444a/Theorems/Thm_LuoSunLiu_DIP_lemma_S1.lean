-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_lemma_S1
-- name    : LuoSunLiu.DIP.lemma_S1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:04.902472+00:00
-- url     : https://prove2.me/theorems/64842f3f-e54c-473c-b4e8-39b527a1f018
-- title:
--   Lemma S1, p. 38 — a positively weighted average of points within δ of each other stays within δ
-- statement:
--   Let $S_1 \subseteq S_2 \subseteq \mathbb N$ with $S_1$ finite and nonempty. Suppose $|a_i - a_j| \le \delta$ for all $i, j \in S_2$, and let $b_i > 0$ for $i \in S_1$. Then for every $j \in S_2$,
--   $$\Bigl|\frac{\sum_{i\in S_1} b_ia_i}{\sum_{i\in S_1} b_i} - a_j\Bigr| \le \delta .$$
--
--   In the proof of Lemma 3 this bounds the distance between the shadow parameter $\dot\xi_t$, a weighted average of past parameters, and the current parameter $\xi_t$ by the perturbation constant.
--
--   **Formalization Note** The paper states $S_2 \subseteq \mathbb N^+$ and does not require $S_1$ nonempty; for empty $S_1$ the weighted average is $0/0$, so nonemptiness (and finiteness) is added. Allowing $0 \in S_2$ only generalizes the statement.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, pp. 38–39, Lemma S1

import Mathlib

namespace LuoSunLiu.DIP

/-- Lemma S1 (Luo, Sun and Liu, arXiv:2109.07340v2, pp. 38–39). If `S₁ ⊆ S₂`, `S₁` is finite and
nonempty, `|a_i - a_j| ≤ δ` for all `i, j ∈ S₂`, and `b_i > 0` for `i ∈ S₁`, then the weighted
average `∑_{i ∈ S₁} b_i a_i / ∑_{i ∈ S₁} b_i` is within `δ` of every `a_j`, `j ∈ S₂`. -/
theorem lemma_S1 (S1 : Finset ℕ) (S2 : Set ℕ) (hS : (S1 : Set ℕ) ⊆ S2) (hne : S1.Nonempty)
    (a b : ℕ → ℝ) (δ : ℝ) (ha : ∀ i ∈ S2, ∀ j ∈ S2, |a i - a j| ≤ δ)
    (hb : ∀ i ∈ S1, 0 < b i) :
    ∀ j ∈ S2, |(∑ i ∈ S1, b i * a i) / (∑ i ∈ S1, b i) - a j| ≤ δ := by sorry

end LuoSunLiu.DIP
