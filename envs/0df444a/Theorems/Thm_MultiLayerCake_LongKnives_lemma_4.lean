-- Prove2me | Theorems.Thm_MultiLayerCake_LongKnives_lemma_4
-- name    : MultiLayerCake.LongKnives.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:00.456849+00:00
-- url     : https://prove2.me/theorems/454ab7ed-1b3c-4cf7-96b5-30030d6f6fda
-- title:
--   Lemma 4, p. 10 — rounding a fractional bipartite assignment to π_{j∗} with a birthday vertex (last bullet for j ≠ j∗)
-- statement:
--   Let $n=N+1\ge1$ and $q$ be positive integers, and let $a_1,\dots,a_q\ge0$ be reals with $\sum_j a_j=n-1$. Let $H=([n-1],[q];E)$ be a bipartite graph with nonnegative edge weights $w_e$ such that
--   $$\sum_{e\in\delta_H(i)}w_e=1\quad(i\in[n-1]),\qquad \sum_{e\in\delta_H(j)}w_e=a_j\quad(j\in[q]).$$
--   Then for every $j^*\in[q]$ there is an assignment $\pi_{j^*}:[n]\to[q]$ such that
--
--   1. $\pi_{j^*}(n)=j^*$;
--   2. for each $i\in[n-1]$, $\pi_{j^*}(i)$ is a neighbour of $i$ in $H$;
--   3. $|\pi_{j^*}^{-1}(j^*)|=\lfloor a_{j^*}\rfloor+1$;
--   4. for each $j\in[q]$ with $j\neq j^*$, $|\pi_{j^*}^{-1}(j)|\in\{\lfloor a_j\rfloor,\lceil a_j\rceil\}$.
--
--   This is the combinatorial half of the proof of Theorem 1: it rounds the fractional assignment produced by the topological lemma to an integral one, reserving the birthday agent's slot at $j^*$.
--
--   **Formalization Note.** The page states the fourth bullet for every $j\in[q]$; at $j=j^*$ with $a_{j^*}$ an integer it contradicts the third (e.g. $n=3$, $q=2$, $a=(1,1)$, $w$ a perfect matching: bullet 3 asks $2$, bullet 4 asks $1$). The proof gives the fourth bullet for $j\ne j^*$, which is what is stated here. The agents are `Fin (N + 1)` with the birthday vertex $n$ as `Fin.last N`; $E$ is a set of pairs, and the weights are a matrix vanishing off $E$.
-- source:
--   Igarashi, Meunier, Envy-Free Division of Multi-Layered Cakes, arXiv:2106.02262v4, p. 10, Lemma 4

import Mathlib

namespace MultiLayerCake.LongKnives

/-- Lemma 4, p. 10, with the last bullet for `j ≠ j∗`: agents `0, …, N − 1` and the birthday vertex
`N` (so `n = N + 1`), a bipartite graph `E ⊆ [N] × [q]` with nonnegative weights `w`, supported on
`E`, with row sums `1` and column sums `a_j ≥ 0` (`Σ_j a_j = N`). Then for every `j∗` there is an
assignment `π : [N + 1] → [q]` with `π(N) = j∗`, every `i < N` sent to a neighbour, `|π⁻¹(j∗)| =
⌊a_{j∗}⌋ + 1`, and `|π⁻¹(j)| ∈ {⌊a_j⌋, ⌈a_j⌉}` for `j ≠ j∗`. -/
theorem lemma_4 {N q : ℕ} (a : Fin q → ℝ) (ha : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = N)
    (E : Set (Fin N × Fin q)) (w : Fin N → Fin q → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hwE : ∀ i j, (i, j) ∉ E → w i j = 0)
    (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = a j) (jStar : Fin q) :
    ∃ π : Fin (N + 1) → Fin q, π (Fin.last N) = jStar ∧ (∀ i : Fin N, (i, π i.castSucc) ∈ E) ∧
      (Finset.univ.filter (fun i => π i = jStar)).card = ⌊a jStar⌋₊ + 1 ∧
      ∀ j, j ≠ jStar → ((Finset.univ.filter (fun i => π i = j)).card = ⌊a j⌋₊ ∨
        (Finset.univ.filter (fun i => π i = j)).card = ⌈a j⌉₊) := by sorry

end MultiLayerCake.LongKnives
