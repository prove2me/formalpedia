-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_theorem_1
-- name    : LookaheadAPI.LeastSquares.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:54:07.467986+00:00
-- url     : https://prove2.me/theorems/7924c917-34da-402e-b07b-a3d68ce8c13d
-- title:
--   Theorem 1 — error bound for least-squares approximate policy iteration with lookahead
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$. Run Algorithm 2 with lookahead $H\ge1$, rollout length $m$, lookahead accuracy $\varepsilon_{LA}$, feature matrix $\Phi\in\mathbb R^{|\mathcal S|\times d}$ and evaluation sets $\mathcal D_k$, and suppose Assumption 1 holds: $\operatorname{rank}\{\phi(i)\}_{i\in\mathcal D_k}=d$ for every $k$, and $\|w_k\|_\infty\le\varepsilon_{PE}$ for all $k$, for some $\varepsilon_{PE}>0$. Let
--   $$\delta_{FV}=\sup_k\|\mathcal M_k\|_\infty=\sup_k\big\|\Phi(\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k})^{-1}\Phi_{\mathcal D_k}^\top\mathcal P_k\big\|_\infty,\qquad \delta_{app}=\sup_{k,\mu}\|\mathcal M_kJ^{\mu}-J^{\mu}\|_\infty,$$
--   $$\beta=\alpha^{m+H-1}\delta_{FV},\qquad \tau=\frac{\alpha^m+\alpha^{m+H-1}}{1-\alpha}\,\delta_{FV}+\delta_{app}+\delta_{FV}\varepsilon_{PE}.$$
--   If
--   $$m+H-1>\frac{\log(\delta_{FV})}{\log(1/\alpha)},$$
--   then for every $k\ge0$ and every deterministic policy $\mu_0$,
--   $$\|J^{\mu_k}-J^*\|_\infty\le\underbrace{\frac{\alpha^{kH}}{1-\alpha}+\frac{2\alpha^H\|J^{\mu_0}-J_0\|_\infty}{1-\alpha}\,k\,\max(\alpha^H,\beta)^{k-1}}_{\text{finite-time component}}+\underbrace{\frac{2\alpha^H\frac{\tau}{1-\beta}+\varepsilon_{LA}}{(1-\alpha^H)(1-\alpha)}}_{\text{asymptotic component}}. \tag{10}$$
--
--   The condition says that the combined lookahead and rollout depth $m+H-1$ must be large enough to offset the amplification $\delta_{FV}$ of the least-squares fit; under it the policies of approximate policy iteration with linear value-function approximation converge geometrically to within the asymptotic component of optimal.
--
--   **Formalization Note** Algorithm 2 never defines $\mu_0$, which appears in the bound; the run's $\mu_0$ is unconstrained, so the bound holds for every deterministic $\mu_0$. $\delta_{app}$ is the supremum over all $k$ and all deterministic policies (the literal reading of $\sup_{k,\mu_k}$). The condition on $m+H-1$ is kept as printed, with Lean's real logarithm; when $\delta_{FV}=0$ (possible only if $d=0$) it reads $m+H-1>0$. At $k=0$ the middle term is $0$.
-- source:
--   arXiv:2109.13419v7, p. 14, Theorem 1, eq. (10)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms

namespace LookaheadAPI.LeastSquares

/-- Theorem 1 (arXiv:2109.13419v7, p. 14, (10)): if `m + H − 1 > log(δ_FV)/log(1/α)`, then under
Assumption 1 every run of Algorithm 2 satisfies, for every `k` (and `μ_0` any deterministic
policy),
`‖J^{μ_k} − J^*‖_∞ ≤ α^{kH}/(1−α) + (2α^H ‖J^{μ_0} − J_0‖_∞/(1−α)) k max(α^H, β)^{k−1}
  + (2α^H τ/(1−β) + ε_LA)/((1−α^H)(1−α))`, with `β = α^{m+H−1}δ_FV` and
`τ = (α^m + α^{m+H−1})/(1−α) δ_FV + δ_app + δ_FV ε_PE`. -/
theorem theorem_1 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE : ℝ)
    (hmH : ((m + H - 1 : ℕ) : ℝ) > Real.log (deltaFV Φ D) / Real.log (1 / M.α))
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hrun : IsRunAlg2 M Φ D m H εLA J μ w θ) (k : ℕ) :
    ‖valueOf M (μ k) - optValue M‖ ≤
      M.α ^ (k * H) / (1 - M.α) +
      2 * M.α ^ H * ‖valueOf M (μ 0) - J 0‖ / (1 - M.α) * k *
        max (M.α ^ H) (betaLS M Φ D m H) ^ (k - 1) +
      (2 * M.α ^ H * (tauLS M Φ D m H εPE / (1 - betaLS M Φ D m H)) + εLA) /
        ((1 - M.α ^ H) * (1 - M.α)) := by sorry

end LookaheadAPI.LeastSquares
