-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_hCount_eq_zero_of_lt
-- name    : HScattered.Hyperplanes.hCount_eq_zero_of_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:48.216994+00:00
-- url     : https://prove2.me/theorems/8488e457-e35e-44b4-94aa-8e726a38ad73
-- title:
--   §5.2 — $h_i = 0$ for $i < rn/s - n$
-- statement:
--   Let $\mathbb F_q \subseteq \mathbb F_{q^n}$ be finite fields, $V = V(r,q^n)$, $h$ a positive integer with $s = h+1$, and $U$ an $h$-scattered $\mathbb F_q$-subspace of $V$ with $\dim_{\mathbb F_q} U = rn/s$. Let $h_i$ be the number of hyperplanes of $V$ meeting $U$ in an $\mathbb F_q$-subspace of dimension $i$. Then
--   $$h_i = 0 \quad\text{for } i < \frac{rn}{s} - n .$$
--
--   Equivalently, every hyperplane meets $U$ in dimension at least $rn/s - n$; this is the lower bound of Theorem 2.7.
--
--   **Formalization Note** $rn/s = \dim_{\mathbb F_q} U$ is encoded by $(h+1)\dim_{\mathbb F_q} U = rn$, and $i < rn/s - n$ by $i + n < \dim_{\mathbb F_q} U$ (no natural-number subtraction).
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 20, §5.2 ("It is easy to see that h_i = 0 for i < rn/s − n")

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

namespace HScattered.Hyperplanes

/-- §5.2 (arXiv:1906.10590v2, p. 20): in the setting of §5.2 (`U` `h`-scattered with
`(h + 1) · dim_F U = r n`, `s = h + 1`), `h_i = 0` for `i < rn/s − n`, written
`i + n < dim_F U`. -/
theorem hCount_eq_zero_of_lt {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K)
    (i : ℕ) (hi : i + Module.finrank F K < Module.finrank F U) :
    hCount F K U i = 0 := by sorry

end HScattered.Hyperplanes
