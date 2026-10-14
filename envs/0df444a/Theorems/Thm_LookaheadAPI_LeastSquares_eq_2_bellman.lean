-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_eq_2_bellman
-- name    : LookaheadAPI.LeastSquares.eq_2_bellman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:12.934887+00:00
-- url     : https://prove2.me/theorems/2912d728-3ba5-4cd3-8b28-bdfc6900843c
-- title:
--   Section 2, eq. (2) — Bellman equations $J^\mu=T_\mu J^\mu$ (unique solution) and $J^*=TJ^*$
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$. For every deterministic policy $\mu$, the value $J^\mu$ is the unique solution of the linear equation
--   $$J^\mu=T_\mu J^\mu, \tag{2}$$
--   that is, $J^\mu$ solves it and every $J\in\mathbb R^{|\mathcal S|}$ with $J=T_\mu J$ equals $J^\mu$. Moreover the optimal reward-to-go solves the Bellman optimality equation
--   $$J^*=TJ^*.$$
--
--   These are the fixed-point characterisations used throughout the analysis of lookahead policy iteration.
--
--   **Formalization Note** $J^\mu$ is defined as the expected discounted series and $J^*$ as the maximum of $J^\mu$ over deterministic policies, so neither equation holds by definition.
-- source:
--   arXiv:2109.13419v7, p. 7, Section 2, eq. (2) and the display J^* = TJ^*

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP

namespace LookaheadAPI.LeastSquares

/-- Section 2, eq. (2) and `J^* = TJ^*` (arXiv:2109.13419v7, p. 7): for every deterministic policy
`μ`, `J^μ` is the unique solution of `J = T_μ J`; and `J^*` solves `J^* = T J^*`. -/
theorem eq_2_bellman {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) :
    (∀ μ : S → A, valueOf M μ = policyOp M μ (valueOf M μ) ∧
      ∀ J : S → ℝ, J = policyOp M μ J → J = valueOf M μ) ∧
    optValue M = bellmanOp M (optValue M) := by sorry

end LookaheadAPI.LeastSquares
