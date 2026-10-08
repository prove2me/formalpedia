-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_theorem_5_2
-- name    : HScattered.Hyperplanes.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:17.494376+00:00
-- url     : https://prove2.me/theorems/ffd6afa0-2694-4174-81bf-341d02797fba
-- title:
--   Theorem 5.2 — the q-binomial theorem (19), (20)
-- statement:
--   Let $q > 1$ and $a, b$ be real numbers and $n \in \mathbb N$. Then
--   $$(ab;q)_n = \sum_{k=0}^{n} b^k\begin{bmatrix} n\\ k\end{bmatrix}_q (a;q)_k (b;q)_{n-k} \qquad (19)$$
--   and
--   $$(ab;q)_n = \sum_{k=0}^{n} a^{n-k}\begin{bmatrix} n\\ k\end{bmatrix}_q (a;q)_k (b;q)_{n-k}. \qquad (20)$$
--
--   These are the two forms of the $q$-binomial theorem (an exercise in Gasper–Rahman, [15, p. 25, Exercise 1.3 (i)]); Corollary 5.3 specialises them.
--
--   **Formalization Note** Stated for real $a, b$ and real $q > 1$, which covers the specialisations used in the paper.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 19, Theorem 5.2 (citing [15, p. 25, Exercise 1.3 (i)])

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_qPoch

namespace HScattered.Hyperplanes

/-- Theorem 5.2 (the `q`-binomial theorem, arXiv:1906.10590v2, p. 19; [15, p. 25, Exercise
1.3 (i)]): for real `a`, `b` and real `q > 1`,
(19) `(ab; q)_n = ∑_{k=0}^n b^k [n k]_q (a; q)_k (b; q)_{n−k}` and
(20) `(ab; q)_n = ∑_{k=0}^n a^{n−k} [n k]_q (a; q)_k (b; q)_{n−k}`. -/
theorem theorem_5_2 (q : ℝ) (hq : 1 < q) (a b : ℝ) (n : ℕ) :
    qPoch (a * b) q n = ∑ k ∈ Finset.range (n + 1),
        b ^ k * gaussBinom q n k * qPoch a q k * qPoch b q (n - k) ∧
      qPoch (a * b) q n = ∑ k ∈ Finset.range (n + 1),
        a ^ (n - k) * gaussBinom q n k * qPoch a q k * qPoch b q (n - k) := by sorry

end HScattered.Hyperplanes
