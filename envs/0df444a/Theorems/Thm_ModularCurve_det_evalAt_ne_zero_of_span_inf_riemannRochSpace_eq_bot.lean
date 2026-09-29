-- Prove2me | Theorems.Thm_ModularCurve_det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot
-- name    : ModularCurve.det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/37a76aa5-e07f-5f42-98dc-ca84f4e7f05b
-- title:
--   Nonvanishing of a determinant of values at rational places
-- statement:
--   Let $N$ be a positive integer and let $\bar F_N =$ `modularFunctionFieldBar N` be the subfield of $\overline{\mathbb{Q}}((q))$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise image of the field $\mathbb{Q}(\mathrm{divisorExpansions}\,N) \subseteq \mathbb{Q}((q))$. Fix $m \in \mathbb{N}$ and a divisor $A$, i.e. a finitely supported function from the places of $\bar F_N/\overline{\mathbb{Q}}$ (valuation subrings of $\bar F_N$ containing $\overline{\mathbb{Q}}$, proper, with principal ideals) to $\mathbb{Z}$. Let $u_0,\dots,u_{m-1} \in \bar F_N$ be linearly independent over $\overline{\mathbb{Q}}$ and lie in the Riemann–Roch space $L(A)$, the space of $f$ with $v(f) \le q^{-A(v)}$ for every place $v$ (valuations normalised through the height-one spectrum of the valuation ring, values in $\mathbb{Z}^{m0}$). Let $P_0,\dots,P_{m-1}$ be pairwise distinct places with $A(P_i) = 0$ for all $i$. Assume the span of the $u_j$ meets $L\bigl(A - \sum_i P_i\bigr)$ only in $0$. Then the $m \times m$ matrix whose $(i,j)$ entry is $(P_i).\mathrm{evalAt}(u_j)$ — the residue of $u_j$ at $P_i$ transported back to $\overline{\mathbb{Q}}$ along the structure map, and $0$ if $u_j \notin P_i$ — has nonzero determinant.
--
--   This is the standard rank criterion for matrices of values of functions in a Riemann–Roch space at degree-one places: distinct points imposing independent conditions on a linear system force the value matrix to be invertible. It is used in the analysis of the height pairing attached to the divisor of $j$, in [`ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.det_evalAt_ne_zero_of_span_inf_riemannRochSpace_eq_bot (N : ℕ) [NeZero N]
    {m : ℕ} (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (u : Fin m → modularFunctionFieldBar N) (hu : LinearIndependent (AlgebraicClosure ℚ) u)
    (huA : ∀ j, u j ∈ riemannRochSpace A)
    (P : Fin m → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hP : Function.Injective P) (hAP : ∀ i, A (P i) = 0)
    (hbot : Submodule.span (AlgebraicClosure ℚ) (Set.range u)
        ⊓ riemannRochSpace (A - ∑ i, Finsupp.single (P i) 1) = ⊥) :
    (Matrix.of fun i j => (P i).evalAt (u j)).det ≠ 0 := by sorry
