-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_eq_15
-- name    : LookaheadAPI.LeastSquares.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:53:58.395132+00:00
-- url     : https://prove2.me/theorems/6e0df983-297f-414f-9abe-c02aa13b9e83
-- title:
--   Appendix A, eq. (15) — one lookahead step with evaluation error $\delta_k$
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, and let $H\ge1$. Let $\mu_k$ be any deterministic policy and $J_k\in\mathbb R^{|\mathcal S|}$ an estimate with $\|J_k-J^{\mu_k}\|_\infty\le\delta_k$. If $\mu_{k+1}$ is an $\varepsilon_{LA}$-accurate $H$-step lookahead policy for $J_k$, i.e. $\|T^HJ_k-T_{\mu_{k+1}}T^{H-1}J_k\|_\infty\le\varepsilon_{LA}$, then
--   $$\|J^{\mu_{k+1}}-J^*\|_\infty\le\alpha^H\|J^{\mu_k}-J^*\|_\infty+\frac{2\alpha^H\delta_k+\varepsilon_{LA}}{1-\alpha}. \tag{15}$$
--
--   This is the one-step contraction of approximate policy iteration with $H$-step lookahead (Efroni et al., 2019, with a time-varying evaluation error); iterating it over $k$ gives Proposition 1.
-- source:
--   arXiv:2109.13419v7, p. 19, Appendix A, eq. (15) (eq. (14), p. 18, is its constant-δ case)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares

/-- Appendix A, eq. (15) (p. 19): if `J_k` is within `δ_k` of `J^{μ_k}` (for any deterministic
policy `μ_k`) and `μ_{k+1}` is an `ε_LA`-accurate `H`-step lookahead policy for `J_k`, then
`‖J^{μ_{k+1}} − J^*‖_∞ ≤ α^H ‖J^{μ_k} − J^*‖_∞ + (2α^H δ_k + ε_LA)/(1 − α)`. -/
theorem eq_15 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (H : ℕ) (hH : 1 ≤ H) (εLA δk : ℝ)
    (Jk : S → ℝ) (μk μk1 : S → A)
    (hδ : ‖Jk - valueOf M μk‖ ≤ δk)
    (hLA : IsLookahead M H εLA Jk μk1) :
    ‖valueOf M μk1 - optValue M‖ ≤
      M.α ^ H * ‖valueOf M μk - optValue M‖ + (2 * M.α ^ H * δk + εLA) / (1 - M.α) := by sorry

end LookaheadAPI.LeastSquares
