-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_proposition_1_geometric
-- name    : LookaheadAPI.LeastSquares.proposition_1_geometric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:54:01.529816+00:00
-- url     : https://prove2.me/theorems/06c6df50-5d66-41ae-8b68-c25e6be44e96
-- title:
--   Proposition 1 (second display) — finite-time and asymptotic components under $\delta_k\le\beta^k\delta_0+\mu$
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, let $H\ge1$, and let $(J_k,\mu_k)_{k\ge0}$ be a run of Algorithm 3 with lookahead accuracy $\varepsilon_{LA}$ and evaluation-error bounds $\delta_k$. Suppose that for some scalars $0<\beta<1$ and $\mu>0$,
--   $$\delta_k\le\beta^k\delta_0+\mu\quad\text{for all }k. \tag{8}$$
--   Then for every $k\ge0$,
--   $$\|J^{\mu_k}-J^*\|_\infty\le\underbrace{\frac{\alpha^{kH}}{1-\alpha}+\frac{2\alpha^H}{1-\alpha}\,k\,\max(\alpha^{H-1},\beta)^{k-1}\delta_0}_{\text{finite-time component}}+\underbrace{\frac{2\alpha^H\mu+\varepsilon_{LA}}{(1-\alpha)(1-\alpha^H)}}_{\text{asymptotic component}}.$$
--
--   When the evaluation errors decay geometrically to a floor $\mu$, the policies converge to within the asymptotic component of optimal; Theorem 1 is this bound with the $\beta$ and $\mu$ of Algorithm 2.
--
--   **Formalization Note** The scalars $\beta,\mu$ of (8) are free, distinct from Theorem 1's $\beta$; the scalar $\mu$ is written `μc` in Lean to avoid a clash with the policies $\mu_k$. At $k=0$ the middle term is $0$.
-- source:
--   arXiv:2109.13419v7, p. 13, Proposition 1 (eq. (8) and second display); proof in Appendix A, p. 19

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares

/-- Proposition 1, second display (p. 13): for every run of Algorithm 3 whose error bounds satisfy
(8), `δ_k ≤ β^k δ_0 + µ` with `0 < β < 1`, `0 < µ` (here `β` and `µ` are free scalars, written
`β` and `μc`), every `k` satisfies
`‖J^{μ_k} − J^*‖_∞ ≤ α^{kH}/(1−α) + (2α^H/(1−α)) k max(α^{H−1}, β)^{k−1} δ_0
  + (2α^H µ + ε_LA)/((1−α)(1−α^H))`. -/
theorem proposition_1_geometric {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A] (M : MDP S A) (H : ℕ) (hH : 1 ≤ H) (εLA : ℝ)
    (δ : ℕ → ℝ) (J : ℕ → S → ℝ) (μ : ℕ → S → A)
    (hrun : IsRunAlg3 M H εLA δ J μ)
    (β μc : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hμc : 0 < μc)
    (h8 : ∀ k : ℕ, δ k ≤ β ^ k * δ 0 + μc) (k : ℕ) :
    ‖valueOf M (μ k) - optValue M‖ ≤
      M.α ^ (k * H) / (1 - M.α) +
      2 * M.α ^ H / (1 - M.α) * k * max (M.α ^ (H - 1)) β ^ (k - 1) * δ 0 +
      (2 * M.α ^ H * μc + εLA) / ((1 - M.α) * (1 - M.α ^ H)) := by sorry

end LookaheadAPI.LeastSquares
