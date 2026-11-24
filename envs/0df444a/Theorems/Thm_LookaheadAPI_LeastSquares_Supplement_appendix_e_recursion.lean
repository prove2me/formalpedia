-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_Supplement_appendix_e_recursion
-- name    : LookaheadAPI.LeastSquares.Supplement.appendix_e_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:54:29.441765+00:00
-- url     : https://prove2.me/theorems/ae719727-ca32-4890-ab65-4ccf9dc42c48
-- title:
--   Appendix E — error recursion $\delta_k\le\beta\delta_{k-1}+\tau$ for Algorithm 4 with the $\beta$, $\tau$ of (12) (corrected: the claim $0<\beta<1$ is not asserted)
-- statement:
--   Consider a run $(\theta_k,J_k,\mu_k,w_k)$ of Algorithm 4 (lookahead depth $H\ge1$, rollout length $m$, step size $\gamma\in\mathbb R$, $\eta$ gradient steps per iteration) under Assumption 1, with $\mu_0$ an arbitrary deterministic policy. Let $\delta_{FV}=\sup_k\|\mathcal M_k\|_\infty$ and $\delta_{app}=\sup_{k,\mu}\|\mathcal M_kJ^\mu-J^\mu\|_\infty$ be the constants of Theorem 1, $\alpha_{GD,\gamma}=\sup_k\max_i|1-\gamma\lambda_i(\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k})|$, $\sigma_{\min,\Phi}$ the smallest singular value of $\Phi$, and
--   $$\beta=\alpha^{m+H-1}\delta_{FV}+\frac{\sqrt{|\mathcal S|}\,\|\Phi\|_\infty}{\sigma_{\min,\Phi}}\alpha_{GD,\gamma}^\eta\big(\alpha^{m+H-1}\delta_{FV}+1\big),$$
--   $$\tau=\Big(1+\frac{\sqrt{|\mathcal S|}\,\|\Phi\|_\infty}{\sigma_{\min,\Phi}}\alpha_{GD,\gamma}^\eta\Big)\Big(\frac{\alpha^m+\alpha^{m+H-1}}{1-\alpha}\delta_{FV}+\delta_{app}+\delta_{FV}\varepsilon_{PE}\Big)+\frac{\sqrt{|\mathcal S|}\,\|\Phi\|_\infty}{(1-\alpha)\sigma_{\min,\Phi}}\alpha_{GD,\gamma}^\eta .$$
--   Then for every $k\ge0$ the evaluation error $\delta_k:=\|J^{\mu_k}-J_k\|_\infty$ satisfies
--   $$\|J^{\mu_{k+1}}-J_{k+1}\|_\infty\le\beta\,\|J_k-J^{\mu_k}\|_\infty+\tau .$$
--
--   No condition on $\gamma$ or $\eta$ is assumed. Together with Proposition 1 this recursion gives Theorem 2; the paper sets $\mu=\tau/(1-\beta)$ when $0<\beta<1$.
--
--   **Formalization Note** $\sigma_{\min,\Phi}$ is $\inf\{\|\Phi x\|_2:\|x\|_2=1\}$ (published `GaussianMatrix.sMin`), the smallest singular value of $\Phi$ because Assumption 1 forces $d\le|\mathcal S|$; $\|\cdot\|_\infty$ of a vector is Lean's sup norm.
--
--   Differences from the source:
--   - reading: the recursion is printed as $\delta_k\le\beta\delta_{k-1}+\tau$ for $J_k$ produced with $\mathcal M_k$ → Lean states it for the step $k\to k+1$ with $J_{k+1}$ produced from $\mathcal D_k$, $\mu_{k+1}$, $w_{k+1}$, for every $k\ge0$; reason: Algorithm 4's Step 4 uses $\mathcal D_k$ at iteration $k$, and the published base mission indexes the same way.
--   - correction: the closing sentence "when $0<\beta<1$, which follows from the assumptions in Proposition 1 and Assumption 2" → not asserted; reason: it is false as printed, since Assumption 2 allows $\alpha_{GD,\gamma}\ge1$ (one state, one action, $r=0$, $\alpha=\tfrac12$, $d=1$, $\phi=1$, $m=2$, $H=1$, $\gamma=-1$, $\eta=1$, $\varepsilon_{PE}=1$ satisfies every printed hypothesis and gives $\beta=\tfrac{11}4$); the corrected Theorem 2 adds $\alpha_{GD,\gamma}<1$, under which $0\le\beta<1$ (see DISPROOF.md).
-- source:
--   arXiv:2109.13419v7, pp. 25–26, Appendix E (recursion after eqs. (22)–(23); β, τ on p. 26); p. 17, eq. (12)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms
import Definitions.Def_LookaheadAPI_LeastSquares_Supplement_Algorithm4
import Definitions.Def_LookaheadAPI_LeastSquares_Supplement_GDConstants

namespace LookaheadAPI.LeastSquares.Supplement

/-- Appendix E, the recursion `δ_k ≤ β δ_{k−1} + τ` (arXiv:2109.13419v7, pp. 25–26; the `β` and
`τ` of (12), p. 17): for every run of Algorithm 4 under Assumption 1 (with `μ_0` any deterministic
policy) and every `k ≥ 0`,
`‖J^{μ_{k+1}} − J_{k+1}‖_∞ ≤ β ‖J_k − J^{μ_k}‖_∞ + τ`, where
`β = α^{m+H−1}δ_FV + (√|𝒮|‖Φ‖_∞/σ_{min,Φ}) α_{GD,γ}^η (α^{m+H−1}δ_FV + 1)` and
`τ = (1 + (√|𝒮|‖Φ‖_∞/σ_{min,Φ}) α_{GD,γ}^η)((α^m + α^{m+H−1})/(1−α) δ_FV + δ_app + δ_FV ε_PE)
  + (√|𝒮|‖Φ‖_∞/((1−α)σ_{min,Φ})) α_{GD,γ}^η`. No condition on `γ` or `η` is assumed. -/
theorem appendix_e_recursion {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE γ : ℝ) (η : ℕ)
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hrun : IsRunAlg4 M Φ D m H εLA γ η J μ w θ) (k : ℕ) :
    ‖valueOf M (μ (k + 1)) - J (k + 1)‖ ≤
      betaGD M Φ D m H γ η * ‖J k - valueOf M (μ k)‖ + tauGD M Φ D m H εPE γ η := by sorry

end LookaheadAPI.LeastSquares.Supplement
