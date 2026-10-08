-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_quantityA_eq_zero
-- name    : HScattered.Hyperplanes.quantityA_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:00.815857+00:00
-- url     : https://prove2.me/theorems/80e225f9-4dc9-46b6-a2a0-7aa7a4e4f3cc
-- title:
--   §5.2/§5.4 — $A = 0$
-- statement:
--   Let $U$ be an $h$-scattered $\mathbb F_q$-subspace of $V = V(r,q^n)$ with $\dim_{\mathbb F_q} U = rn/s$, where $s = h+1$, and let $h_i$ be the number of hyperplanes of $V$ meeting $U$ in an $\mathbb F_q$-subspace of dimension $i$. Then
--   $$A := \sum_i h_i (q^n-1)(q^i - q^{n(r-s)/s})(q^i - q^{n(r-s)/s+1})\cdots(q^i - q^{n(r-s)/s+s-1}) = 0 .$$
--
--   As the paper notes (p. 20), this vanishing yields $h_i = 0$ for $i > n(r-s)/s + s - 1$, which is the upper bound of Theorem 2.7.
--
--   **Formalization Note** $n(r-s)/s$ is written $\dim_{\mathbb F_q} U - n$ (exact here, as $\dim_{\mathbb F_q} U \ge n$); the identity is in $\mathbb Z$ with $q = |\mathbb F_q|$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 20, §5.2 ("Our aim is to prove A := … = 0"), proved in §5.4, pp. 23–24

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

namespace HScattered.Hyperplanes

/-- §5.2, p. 20 ("Our aim is to prove"), proved in §5.4 (arXiv:1906.10590v2, pp. 23–24): in the
setting of §5.2 (`s = h + 1`, `dim_F U = rn/s`),
`A = ∑_i h_i (qⁿ − 1)(q^i − q^{n(r−s)/s})⋯(q^i − q^{n(r−s)/s + s − 1}) = 0`. -/
theorem quantityA_eq_zero {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K) :
    quantityA F K h U = 0 := by sorry

end HScattered.Hyperplanes
