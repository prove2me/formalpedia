-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_eq_3_4
-- name    : LookaheadAPI.LeastSquares.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:12.64998+00:00
-- url     : https://prove2.me/theorems/6340036d-c29f-4547-bd6b-194e029d0eca
-- title:
--   Section 2, eqs. (3)–(4) — shift and monotonicity of $T$ and $T_\mu$
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, and let $e\in\mathbb R^{|\mathcal S|}$ be the all-ones vector. For every deterministic policy $\mu$, every $c\in\mathbb R$ and all $J,J'\in\mathbb R^{|\mathcal S|}$:
--
--   1. (shift, (3)) $$T(J+ce)=TJ+\alpha ce,\qquad T_\mu(J+ce)=T_\mu J+\alpha ce;$$
--   2. (monotonicity, (4)) if $J\le J'$ componentwise, then $TJ\le TJ'$ and $T_\mu J\le T_\mu J'$.
--
--   These two properties are the elementary tools of every error estimate for (approximate) policy iteration.
-- source:
--   arXiv:2109.13419v7, p. 7, Section 2, eqs. (3) and (4)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP

namespace LookaheadAPI.LeastSquares

/-- Section 2, eqs. (3)–(4) (p. 7): with `e` the all-ones vector, `T(J + ce) = TJ + αce` and
`T_μ(J + ce) = T_μJ + αce`; and `T`, `T_μ` are monotone for the pointwise order. -/
theorem eq_3_4 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) :
    (∀ (μ : S → A) (c : ℝ) (J : S → ℝ),
      bellmanOp M (J + fun _ => c) = bellmanOp M J + (fun _ => M.α * c) ∧
      policyOp M μ (J + fun _ => c) = policyOp M μ J + (fun _ => M.α * c)) ∧
    (∀ (μ : S → A) (J J' : S → ℝ), J ≤ J' →
      bellmanOp M J ≤ bellmanOp M J' ∧ policyOp M μ J ≤ policyOp M μ J') := by sorry

end LookaheadAPI.LeastSquares
