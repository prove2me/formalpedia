-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_lemma_5_7
-- name    : HScattered.Hyperplanes.lemma_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:47.388969+00:00
-- url     : https://prove2.me/theorems/701ae33f-e7ed-4791-be59-477ac7ec0027
-- title:
--   Lemma 5.7 — the double count of independent points on hyperplanes
-- statement:
--   Let $U$ be an $h$-scattered $\mathbb F_q$-subspace of $V = V(r,q^n)$ with $\dim_{\mathbb F_q} U = rn/s$, where $s = h+1$, and let $h_i$ be the number of hyperplanes of $V$ meeting $U$ in an $\mathbb F_q$-subspace of dimension $i$. Then for every $k \in \{0,1,\dots,s-1\}$,
--   $$\sum_i h_i (q^n-1)(q^i-1)(q^i-q)(q^i-q^2)\cdots(q^i-q^k) = (q^{rn/s}-1)(q^{rn/s}-q)(q^{rn/s}-q^2)\cdots(q^{rn/s}-q^k)\,(q^{(r-k-1)n}-1).$$
--
--   Together with Lemma 5.5 and Theorem 5.6 it determines the moments $\alpha_k$ of the distribution $(h_i)$ for $k \le s$.
--
--   **Formalization Note** The identity is stated in $\mathbb Z$ with $q = |\mathbb F_q|$ and $q^{rn/s} = q^{\dim_{\mathbb F_q} U}$. The range $k \le s-1 = h$ is kept; since $h < r$, $r - k - 1$ is a genuine natural number.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 20, Lemma 5.7

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

namespace HScattered.Hyperplanes

/-- Lemma 5.7 (arXiv:1906.10590v2, p. 20): in the setting of §5.2 (`s = h + 1`,
`dim_F U = rn/s`), for every `k ∈ {0, 1, …, s − 1}`,
`∑_i h_i (qⁿ − 1)(q^i − 1)(q^i − q)⋯(q^i − q^k)
  = (q^{rn/s} − 1)(q^{rn/s} − q)⋯(q^{rn/s} − q^k)(q^{(r−k−1)n} − 1)`.
Since `k ≤ h < r`, `r − k − 1` is an honest natural number. -/
theorem lemma_5_7 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (k : ℕ) (hk : k < h + 1) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1),
        (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) *
          ∏ j ∈ Finset.range (k + 1), ((Fintype.card F : ℤ) ^ i - (Fintype.card F : ℤ) ^ j) =
      (∏ j ∈ Finset.range (k + 1),
          ((Fintype.card F : ℤ) ^ Module.finrank F U - (Fintype.card F : ℤ) ^ j)) *
        ((Fintype.card F : ℤ) ^ ((Module.finrank K V - k - 1) * Module.finrank F K) - 1) := by sorry

end HScattered.Hyperplanes
