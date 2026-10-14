-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_contraction_T
-- name    : LookaheadAPI.LeastSquares.contraction_T
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:09.525881+00:00
-- url     : https://prove2.me/theorems/68e1435f-6d1c-4ea3-903d-2edaa29c88d6
-- title:
--   Section 2, p. 6 — $\|TJ-J^*\|_\infty\le\alpha\|J-J^*\|_\infty$
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, with Bellman operator $T$ and optimal reward-to-go $J^*$. For every vector $J\in\mathbb R^{|\mathcal S|}$,
--   $$\|TJ-J^*\|_\infty\le\alpha\,\|J-J^*\|_\infty .$$
--
--   Each application of $T$ brings an estimate closer to $J^*$ in sup norm; iterated, $\|T^HJ-J^*\|_\infty\le\alpha^H\|J-J^*\|_\infty$, which is the source of the factors $\alpha^H$ and $\alpha^{H-1}$ in the bounds of the paper.
-- source:
--   arXiv:2109.13419v7, p. 6, Section 2 (unnumbered display ‖TJ − J^*‖∞ ≤ α‖J − J^*‖∞)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP

namespace LookaheadAPI.LeastSquares

/-- Section 2, p. 6: one application of the Bellman operator contracts the sup-norm distance to
`J^*` by `α`: `‖TJ − J^*‖_∞ ≤ α ‖J − J^*‖_∞` for every `J ∈ ℝ^{|𝒮|}`. -/
theorem contraction_T {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (J : S → ℝ) :
    ‖bellmanOp M J - optValue M‖ ≤ M.α * ‖J - optValue M‖ := by sorry

end LookaheadAPI.LeastSquares
