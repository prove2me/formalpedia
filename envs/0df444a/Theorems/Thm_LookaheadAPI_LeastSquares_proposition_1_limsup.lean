-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_proposition_1_limsup
-- name    : LookaheadAPI.LeastSquares.proposition_1_limsup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:54:04.176967+00:00
-- url     : https://prove2.me/theorems/8ca8104d-160d-4892-ad4a-e357ad3464be
-- title:
--   Proposition 1 (third display) — $\limsup_k\|J^{\mu_k}-J^*\|_\infty\le(2\alpha^H\mu+\varepsilon_{LA})/((1-\alpha)(1-\alpha^H))$
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, let $H\ge1$, and let $(J_k,\mu_k)_{k\ge0}$ be a run of Algorithm 3 with lookahead accuracy $\varepsilon_{LA}$ and evaluation-error bounds $\delta_k$ satisfying (8): $\delta_k\le\beta^k\delta_0+\mu$ for all $k$, with $0<\beta<1$ and $\mu>0$. Then
--   $$\limsup_{k\to\infty}\|J^{\mu_k}-J^*\|_\infty\le\frac{2\alpha^H\mu+\varepsilon_{LA}}{(1-\alpha)(1-\alpha^H)}.$$
--
--   The finite-time component of the error vanishes in the limit and only the floor set by the evaluation error $\mu$ and the lookahead error remains.
--
--   **Formalization Note** The sequence $\|J^{\mu_k}-J^*\|_\infty$ is bounded, and the limsup bound is stated in its elementary form: for every $\varepsilon>0$, eventually $\|J^{\mu_k}-J^*\|_\infty\le\frac{2\alpha^H\mu+\varepsilon_{LA}}{(1-\alpha)(1-\alpha^H)}+\varepsilon$.
-- source:
--   arXiv:2109.13419v7, p. 13, Proposition 1 (third display)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares

/-- Proposition 1, third display (p. 13): under (8) with `0 < β < 1`, `0 < µ`,
`limsup_{k→∞} ‖J^{μ_k} − J^*‖_∞ ≤ (2α^H µ + ε_LA)/((1−α)(1−α^H))`, stated as: for every
`ε > 0`, eventually `‖J^{μ_k} − J^*‖_∞ ≤ (2α^H µ + ε_LA)/((1−α)(1−α^H)) + ε`. -/
theorem proposition_1_limsup {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : MDP S A) (H : ℕ) (hH : 1 ≤ H) (εLA : ℝ)
    (δ : ℕ → ℝ) (J : ℕ → S → ℝ) (μ : ℕ → S → A)
    (hrun : IsRunAlg3 M H εLA δ J μ)
    (β μc : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hμc : 0 < μc)
    (h8 : ∀ k : ℕ, δ k ≤ β ^ k * δ 0 + μc) :
    ∀ ε > 0, ∀ᶠ k in Filter.atTop,
      ‖valueOf M (μ k) - optValue M‖ ≤
        (2 * M.α ^ H * μc + εLA) / ((1 - M.α) * (1 - M.α ^ H)) + ε := by sorry

end LookaheadAPI.LeastSquares
