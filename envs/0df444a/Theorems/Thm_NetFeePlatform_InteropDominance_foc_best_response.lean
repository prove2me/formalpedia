-- Prove2me | Theorems.Thm_NetFeePlatform_InteropDominance_foc_best_response
-- name    : NetFeePlatform.InteropDominance.foc_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:14.043302+00:00
-- url     : https://prove2.me/theorems/c2893524-9da9-4fb0-ad3b-20b289a74816
-- title:
--   Appendix E.1.3, p. 47, with (36), p. 43 — if γ(1 − λ) ≤ 27/8, a net fee satisfying (20) is a best response in the Logit duopoly
-- statement:
--   Consider the Logit duopoly without outside option, with marginal cost $c$, network-interaction value $\gamma$ and interoperability $\lambda\in[0,1]$, and assume
--
--   $$\gamma(1-\lambda)\le\frac{27}{8}.$$
--
--   Let $t=(t^1,t^2)$ be a fee profile and $j$ a platform whose net fee satisfies the first-order condition (20),
--   $t^j=c+\frac{1}{1-n^j}-2\gamma n^j-\gamma\lambda(1-n^j)+\gamma\lambda n^j$. Then $t^j$ is a best response to the other platform's fee: for every $s\in\mathbb R$,
--
--   $$\pi^j(t^{-j},s)\le\pi^j(t).$$
--
--   In the appendix the second derivative of profit in the own share is $-1/(n^j(1-n^j)^2)+2\gamma(1-\lambda\varphi^j)$, with diversion ratio $\varphi^j=1$ here; since $1/(n(1-n)^2)\ge 27/4$ on $(0,1)$ (display (36)), the condition $\gamma(1-\lambda)\le 27/8$ makes profit concave in the own share, so the first-order condition is sufficient.
--
--   **Formalization Note** The bound $27/8$ is the paper's $3.375$, half the minimum $6.75=27/4$ of $1/(n(1-n)^2)$ attained at $n=1/3$ ((36), p. 43).
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), pp. 46–47, Appendix E.1.3; p. 43, (36)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropDominance

theorem foc_best_response (c γ lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hreg : γ * (1 - lam) ≤ 27 / 8) (t : Fin 2 → ℝ) (j : Fin 2)
    (hfoc : t j = c + 1 / (1 - NetFeePlatform.Competition.demand 0 t j) - 2 * γ * NetFeePlatform.Competition.demand 0 t j
      - γ * lam * (1 - NetFeePlatform.Competition.demand 0 t j) + γ * lam * NetFeePlatform.Competition.demand 0 t j) :
    ∀ s : ℝ, NetFeePlatform.Competition.profit 0 c γ lam (Function.update t j s) j ≤ NetFeePlatform.Competition.profit 0 c γ lam t j := by sorry

end NetFeePlatform.InteropDominance
