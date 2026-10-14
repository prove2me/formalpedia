-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_proposition_1
-- name    : LookaheadAPI.LeastSquares.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:53:43.21605+00:00
-- url     : https://prove2.me/theorems/4e87a9be-0a86-4831-823d-952f5b1c3824
-- title:
--   Proposition 1 (first display) — error bound for Algorithm 3 with time-varying evaluation error
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, let $H\ge2$, and let $(J_k,\mu_k)_{k\ge0}$ be a run of Algorithm 3 with lookahead accuracy $\varepsilon_{LA}$ and evaluation-error bounds $\delta_k$, i.e. $\|T^HJ_k-T_{\mu_{k+1}}T^{H-1}J_k\|_\infty\le\varepsilon_{LA}$ and $\|J_k-J^{\mu_k}\|_\infty\le\delta_k$ for every $k$. Then for every $k\ge0$,
--   $$\|J^{\mu_k}-J^*\|_\infty\le\frac{\alpha^{kH}}{1-\alpha}+\sum_{\ell=0}^{k-1}\frac{\alpha^{(k-\ell-1)H}\,2\alpha^H\delta_\ell}{1-\alpha}+\frac{\varepsilon_{LA}}{(1-\alpha)(1-\alpha^{H-1})}.$$
--
--   The bound separates the effect of the initial policy, the accumulated evaluation errors, and the lookahead error.
--
--   **Formalization Note** The last term divides by $1-\alpha^{H-1}$, which vanishes at $H=1$ (the bound is $+\infty$ there on paper, while Lean's $x/0=0$ would make it false), so this item assumes $H\ge2$. $\mu_0$ is an arbitrary deterministic policy, and the index of $\delta_k$ is that of (15) and Appendix B (see the `Algorithms` module).
-- source:
--   arXiv:2109.13419v7, p. 13, Proposition 1 (first display); proof in Appendix A, p. 19, eq. (16)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares

/-- Proposition 1, first display (p. 13): every run of Algorithm 3 with `H ≥ 2` satisfies
`‖J^{μ_k} − J^*‖_∞ ≤ α^{kH}/(1−α) + ∑_{ℓ=0}^{k−1} α^{(k−ℓ−1)H} 2α^H δ_ℓ/(1−α)
  + ε_LA/((1−α)(1−α^{H−1}))` for every `k`. -/
theorem proposition_1 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) (H : ℕ) (hH : 2 ≤ H) (εLA : ℝ)
    (δ : ℕ → ℝ) (J : ℕ → S → ℝ) (μ : ℕ → S → A)
    (hrun : IsRunAlg3 M H εLA δ J μ) (k : ℕ) :
    ‖valueOf M (μ k) - optValue M‖ ≤
      M.α ^ (k * H) / (1 - M.α) +
      ∑ ℓ ∈ Finset.range k, M.α ^ ((k - ℓ - 1) * H) * (2 * M.α ^ H * δ ℓ) / (1 - M.α) +
      εLA / ((1 - M.α) * (1 - M.α ^ (H - 1))) := by sorry

end LookaheadAPI.LeastSquares
