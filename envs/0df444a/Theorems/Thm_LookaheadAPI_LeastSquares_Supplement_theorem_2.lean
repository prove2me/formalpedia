-- Prove2me | Theorems.Thm_LookaheadAPI_LeastSquares_Supplement_theorem_2
-- name    : LookaheadAPI.LeastSquares.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T06:55:34.151369+00:00
-- url     : https://prove2.me/theorems/883837fa-8d1d-4173-98cc-af53a8410470
-- title:
--   Theorem 2 (corrected: adds $\alpha_{GD,\gamma}<1$) — error bound (13) for approximate policy iteration with lookahead and gradient-descent policy evaluation
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\alpha)$ be a finite discounted MDP with rewards in $[0,1]$ and $0<\alpha<1$, $\Phi\in\mathbb R^{|\mathcal S|\times d}$ a feature matrix and $\mathcal D_k$ the evaluation sets. Run Algorithm 4: at iteration $k$, take an $\varepsilon_{LA}$-accurate $H$-step lookahead policy $\mu_{k+1}$ for $J_k$ ($H\ge1$), form the noisy $m$-step return $\hat J^{\mu_{k+1}}=T^m_{\mu_{k+1}}T^{H-1}J_k+w_{k+1}$ on $\mathcal D_k$, take $\eta$ gradient steps of size $\gamma$ on the least-squares objective starting from $\theta_k$, and set $J_{k+1}=\Phi\theta_{k+1}$, with $J_0=\Phi\theta_0$; $\mu_0$ is an arbitrary deterministic policy. Let $\delta_{FV}=\sup_k\|\mathcal M_k\|_\infty$, $\delta_{app}=\sup_{k,\mu}\|\mathcal M_kJ^\mu-J^\mu\|_\infty$, and let $\alpha_{GD,\gamma}$, $\sigma_{\min,\Phi}$, $\beta$ and $\tau$ be as in (12):
--   $$\beta=\alpha^{m+H-1}\delta_{FV}+\frac{\sqrt{|\mathcal S|}\,\|\Phi\|_\infty}{\sigma_{\min,\Phi}}\alpha_{GD,\gamma}^\eta\big(\alpha^{m+H-1}\delta_{FV}+1\big),$$
--   $$\tau=\Big(1+\frac{\sqrt{|\mathcal S|}\,\|\Phi\|_\infty}{\sigma_{\min,\Phi}}\alpha_{GD,\gamma}^\eta\Big)\Big(\frac{\alpha^m+\alpha^{m+H-1}}{1-\alpha}\delta_{FV}+\delta_{app}+\delta_{FV}\varepsilon_{PE}\Big)+\frac{\sqrt{|\mathcal S|}\,\|\Phi\|_\infty}{(1-\alpha)\sigma_{\min,\Phi}}\alpha_{GD,\gamma}^\eta .$$
--
--   Suppose that $m+H-1>\log(2\delta_{FV})/\log(1/\alpha)$, that Assumptions 1 and 2 hold, and that $\alpha_{GD,\gamma}<1$. Then for every $k$,
--   $$\|J^{\mu_k}-J^*\|_\infty\le\frac{\alpha^{kH}}{1-\alpha}+\frac{2\alpha^H\|J^{\mu_0}-J_0\|_\infty}{1-\alpha}\,k\max(\alpha^H,\beta)^{k-1}+\frac{2\alpha^H\frac{\tau}{1-\beta}+\varepsilon_{LA}}{(1-\alpha^H)(1-\alpha)} .$$
--
--   The first two terms form the finite-time component and the last the asymptotic component. As $\eta\to\infty$ the bound becomes that of Theorem 1 for least-squares evaluation (Remark 3).
--
--   **Formalization Note** Logarithms are real logarithms (Lean's $\log0=0$); $k\max(\alpha^H,\beta)^{k-1}$ uses natural-number subtraction, which only matters at $k=0$, where the factor $k$ is $0$. $\sigma_{\min,\Phi}$ is $\inf\{\|\Phi x\|_2:\|x\|_2=1\}$. The first clause of Assumption 2 is stated as $\gamma\cdot d\inf_k\|\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k}\|_\infty^2<1$ (see the definition item).
--
--   Differences from the source:
--   - correction: under the printed hypotheses alone (Assumptions 1–2 and $m+H-1>\log(2\delta_{FV})/\log(1/\alpha)$) → Lean adds the premise $\alpha_{GD,\gamma}<1$; reason: the printed theorem is false, since Assumption 2 bounds $\gamma$ only from above, and then $\log(1/\alpha_{GD,\gamma})\le0$ makes the $\eta$-clause vacuous and $\beta>1$. Counterexample: one state, one action, $r=0$, $\alpha=\tfrac12$, $d=1$, $\phi=1$, $\mathcal D_k=\mathcal S$, $m=2$, $H=1$, $\gamma=-1$, $\eta=1$, $\varepsilon_{PE}=\varepsilon_{LA}=1$, $w=0$ satisfies every printed hypothesis with $\alpha_{GD,\gamma}=2$, $\beta=\tfrac{11}4$, $\tau=10$, and at $k=0$ the right side is $2-\tfrac{132}7<0=\|J^{\mu_0}-J^*\|_\infty$; with $\phi=0.3$, $\gamma=100>0$ the right side is again negative. The paper's proof asserts $\alpha_{GD,\gamma}<1$ (p. 24) and uses it to get $\beta<1$ (p. 26); the premise excludes exactly the step sizes with $\alpha_{GD,\gamma}\ge1$.
--   - reading: the first clause of Assumption 2, $\gamma<1/(d\inf_k\|\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k}\|_\infty^2)$ → $\gamma\cdot d\inf_k\|\Phi_{\mathcal D_k}^\top\Phi_{\mathcal D_k}\|_\infty^2<1$; reason: equivalent when the denominator is positive (always, under Assumption 1, when $d\ge1$); at $d=0$ the printed $1/0$ is read as $+\infty$.
--   - reading: $\log(2\delta_{FV})$ and the logarithms of Assumption 2 → Lean's real logarithm with $\log0=0$; reason: $\delta_{FV}=0$ only when $d=0$ under Assumption 1, where the paper's $\log0=-\infty$ would make the condition vacuous and Lean's reads $m+H-1>0$; the same convention as the published Theorem 1.
--   - reading: $\mathcal M_k$ and the iteration index of Algorithm 4 → $J_{k+1}$ is produced from $\mathcal D_k$, $\mu_{k+1}$, $w_{k+1}$, and $\mu_0$ is an arbitrary deterministic policy; reason: Algorithm 4 as printed, and the published base mission's convention.
-- source:
--   arXiv:2109.13419v7, p. 17, Theorem 2, eq. (13) (Assumption 2 on pp. 16–17; β, τ of (12) on p. 17; proof via Appendix E, pp. 23–26, and Proposition 1, p. 13)

import Mathlib
import Definitions.Def_LookaheadAPI_LeastSquares_MDP
import Definitions.Def_LookaheadAPI_LeastSquares_LSOperator
import Definitions.Def_LookaheadAPI_LeastSquares_Algorithms
import Definitions.Def_LookaheadAPI_LeastSquares_Supplement_Algorithm4
import Definitions.Def_LookaheadAPI_LeastSquares_Supplement_GDConstants

namespace LookaheadAPI.LeastSquares.Supplement

/-- Theorem 2 (arXiv:2109.13419v7, p. 17, (13)), corrected: if `m + H − 1 > log(2δ_FV)/log(1/α)`,
then under Assumptions 1–2 and the added premise `α_{GD,γ} < 1` (asserted on p. 24 of the
paper's proof; without it the printed theorem is false), every run of Algorithm 4 satisfies, for
every `k` (and `μ_0` any deterministic policy),
`‖J^{μ_k} − J^*‖_∞ ≤ α^{kH}/(1−α) + (2α^H ‖J^{μ_0} − J_0‖_∞/(1−α)) k max(α^H, β)^{k−1}
  + (2α^H τ/(1−β) + ε_LA)/((1−α^H)(1−α))`, with the gradient-descent `β` and `τ` of (12). -/
theorem theorem_2 {S A : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A]
    [DecidableEq A] [Nonempty A] (M : MDP S A) {d : ℕ} (Φ : Matrix S (Fin d) ℝ)
    (D : ℕ → Finset S) (m H : ℕ) (hH : 1 ≤ H) (εLA εPE γ : ℝ) (η : ℕ)
    (hmH : ((m + H - 1 : ℕ) : ℝ) > Real.log (2 * deltaFV Φ D) / Real.log (1 / M.α))
    (J : ℕ → S → ℝ) (μ : ℕ → S → A) (w : ℕ → S → ℝ) (θ : ℕ → Fin d → ℝ)
    (hA1 : Assumption1 Φ D w εPE)
    (hA2 : Assumption2 M Φ D m H γ η)
    (hGD : alphaGD Φ D γ < 1)
    (hrun : IsRunAlg4 M Φ D m H εLA γ η J μ w θ) (k : ℕ) :
    ‖valueOf M (μ k) - optValue M‖ ≤
      M.α ^ (k * H) / (1 - M.α) +
      2 * M.α ^ H * ‖valueOf M (μ 0) - J 0‖ / (1 - M.α) * k *
        max (M.α ^ H) (betaGD M Φ D m H γ η) ^ (k - 1) +
      (2 * M.α ^ H * (tauGD M Φ D m H εPE γ η / (1 - betaGD M Φ D m H γ η)) + εLA) /
        ((1 - M.α ^ H) * (1 - M.α)) := by sorry

end LookaheadAPI.LeastSquares.Supplement
