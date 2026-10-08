-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_theorem_5_6
-- name    : HScattered.Hyperplanes.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:55.035722+00:00
-- url     : https://prove2.me/theorems/52df6fe0-b8d4-4b88-aa93-6931ba86eb4e
-- title:
--   Theorem 5.6 — Carlitz's q-binomial inverse formula
-- statement:
--   Let $q > 1$ be real and let $(a_k)_{k \ge 0}$, $(b_k)_{k \ge 0}$ be sequences of complex numbers. Then
--   $$a_k = \sum_{j=0}^{k} (-1)^j q^{j(j-1)/2}\begin{bmatrix} k\\ j\end{bmatrix}_q b_j \ \text{ for all } k$$
--   if and only if
--   $$b_k = \sum_{j=0}^{k} (-1)^j q^{j(j+1)/2 - jk}\begin{bmatrix} k\\ j\end{bmatrix}_q a_j \ \text{ for all } k .$$
--
--   This inversion formula (a special case of [7, Theorem 2]) is what turns the expression of $\beta_k$ through the $\alpha_j$ into equation (24).
--
--   **Formalization Note** "If … then … and vice versa" is read as an equivalence between the two families of identities over all $k \ge 0$. The exponent $j(j+1)/2 - jk = \binom{j}{2} + j - jk$ may be negative, so it is an integer power of $q$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 19, Theorem 5.6 (citing [7, Theorem 2, p. 897, (4.2) and (4.3)])

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom

namespace HScattered.Hyperplanes

/-- Theorem 5.6 (arXiv:1906.10590v2, p. 19; Carlitz's `q`-binomial inverse formula,
[7, Theorem 2]): for real `q > 1` and complex sequences `(a_k)`, `(b_k)`,
`a_k = ∑_{j=0}^k (−1)^j q^{j(j−1)/2} [k j]_q b_j` for all `k` if and only if
`b_k = ∑_{j=0}^k (−1)^j q^{j(j+1)/2 − jk} [k j]_q a_j` for all `k`
(`j(j−1)/2 = C(j, 2)` and `j(j+1)/2 − jk = C(j, 2) + j − jk`, an integer exponent). -/
theorem theorem_5_6 (q : ℝ) (hq : 1 < q) (a b : ℕ → ℂ) :
    (∀ k : ℕ, a k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (gaussBinom q k j : ℂ) * b j) ↔
      (∀ k : ℕ, b k = ∑ j ∈ Finset.range (k + 1),
        (-1 : ℂ) ^ j * (q : ℂ) ^ ((j.choose 2 : ℤ) + j - (j : ℤ) * k) *
          (gaussBinom q k j : ℂ) * a j) := by sorry

end HScattered.Hyperplanes
