-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_eq_23
-- name    : HScattered.Hyperplanes.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:45.034543+00:00
-- url     : https://prove2.me/theorems/d7a0479c-fe3a-4a8e-a7b4-1f803531673d
-- title:
--   Equation (23) — $\sum_i h_i(q^n-1) = q^{rn}-1$
-- statement:
--   In the setting of §5.2 ($U$ an $h$-scattered $\mathbb F_q$-subspace of $V = V(r,q^n)$ of dimension $rn/(h+1)$, and $h_i$ the number of hyperplanes of $V$ meeting $U$ in dimension $i$), the total number of hyperplanes is $(q^{rn}-1)/(q^n-1) = \sum_i h_i$, hence
--   $$\sum_i h_i (q^n - 1) = q^{rn} - 1 .$$
--
--   This is the case $k = 0$ normalisation $\alpha_0 = \beta_0 = q^{rn} - 1$ used in §5.3.
--
--   **Formalization Note** $q = |\mathbb F_q|$; the sum runs over $0 \le i \le \dim_{\mathbb F_q} U$; the identity is in $\mathbb Z$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 20, equation (23)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_IsHScattered
import Definitions.Def_HScattered_Hyperplanes_hyperplaneCounts

namespace HScattered.Hyperplanes

/-- Equation (23) (arXiv:1906.10590v2, p. 20): in the setting of §5.2, the hyperplanes of
`V(r, qⁿ)` number `(q^{rn} − 1)/(qⁿ − 1) = ∑_i h_i`, so `∑_i h_i (qⁿ − 1) = q^{rn} − 1`
(`q = |F|`, `n = finrank F K`, `r = finrank K V`). -/
theorem eq_23 {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (U : Submodule F V) (hU : IsHScattered F K h U)
    (hdim : (h + 1) * Module.finrank F U = Module.finrank K V * Module.finrank F K) :
    ∑ i ∈ Finset.range (Module.finrank F U + 1),
        (hCount F K U i : ℤ) * ((Fintype.card F : ℤ) ^ Module.finrank F K - 1) =
      (Fintype.card F : ℤ) ^ (Module.finrank K V * Module.finrank F K) - 1 := by sorry

end HScattered.Hyperplanes
