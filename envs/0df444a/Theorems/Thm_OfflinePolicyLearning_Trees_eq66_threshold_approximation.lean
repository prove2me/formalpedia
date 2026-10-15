-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_eq66_threshold_approximation
-- name    : OfflinePolicyLearning.Trees.eq66_threshold_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:38.711037+00:00
-- url     : https://prove2.me/theorems/ae8adfba-475b-46f8-b2b1-ca3e5327ac15
-- title:
--   (66), p. 67 — ⌈L/ε⌉ thresholds approximate every threshold indicator within Hamming distance ε/L
-- statement:
--   For $b\in\mathbb R$ let $\mathbf 1_b(r)=1$ if $r<b$ and $0$ if $r\ge b$. Let $L\ge1$ be an integer, $\varepsilon>0$, $m\ge1$, and let $r_1,\dots,r_m$ be real numbers (repetitions allowed). Then there are $K=\lceil L/\varepsilon\rceil$ thresholds $b_1,\dots,b_K$ such that for every $b\in\mathbb R$
--   $$\min_{1\le i\le K}\ \frac1m\sum_{j=1}^m\big|\mathbf 1_b(r_j)-\mathbf 1_{b_i}(r_j)\big|\ \le\ \frac{\varepsilon}{L}.$$
--
--   This is the one-dimensional approximation step behind the covering bound for decision trees: a single branch node's threshold can be replaced by one of $\lceil L/\varepsilon\rceil$ fixed thresholds at a Hamming cost of at most $\varepsilon/L$.
--
--   **Formalization Note** The thresholds are indexed by `Fin ⌈L/ε⌉₊`. The paper's display writes the minimum over $i\in\{1,\dots,n\}$, a slip for $i\in\{1,\dots,\lceil L/\varepsilon\rceil\}$. The paper's proof removes duplicate $r_j$ "without loss of generality", which changes the normalization $1/m$; the statement here keeps the multiplicities, which is the form the tree argument applies to.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 67, App. F, Step 1, display (66)

import Mathlib

namespace OfflinePolicyLearning.Trees

/-- (66), p. 67 (App. F, Step 1): for any `m` reals `r_1, …, r_m` (repetitions allowed) there are
`⌈L/ε⌉` thresholds `b'_i` such that every threshold indicator `1_b(r) = 1{r < b}` is within
Hamming distance `ε/L` of some `1_{b'_i}` with respect to `r_1, …, r_m`. -/
theorem eq66_threshold_approximation (L : ℕ) (hL : 1 ≤ L) (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : 1 ≤ m) (r : Fin m → ℝ) :
    ∃ b' : Fin ⌈(L : ℝ) / ε⌉₊ → ℝ, ∀ b : ℝ, ∃ i,
      (1 / (m : ℝ)) * ((Finset.univ.filter fun j => ¬ (r j < b ↔ r j < b' i)).card : ℝ)
        ≤ ε / L := by sorry

end OfflinePolicyLearning.Trees
