-- Prove2me | Theorems.Thm_NetFeePlatform_InteropFee_foc_best_response
-- name    : NetFeePlatform.InteropFee.foc_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:34.055473+00:00
-- url     : https://prove2.me/theorems/26a4e9fb-a041-40a1-a011-89431ba824ea
-- title:
--   Appendix E.1.3, p. 47, with (36), p. 43 — under Logit demand and γ ≤ 27/8, the interoperability FOC (33) gives a global best response
-- statement:
--   Consider $J$ platforms with Logit demand and outside-option weight $w \ge 0$, where $w > 0$ or $J \ge 2$. Let $c$ be the marginal cost, $\gamma \le 27/8$ the interaction value and $\lambda \in [0,1]$ the interoperability degree. Fix a net-fee profile $t$ and a platform $j$, and write $n^j = n^j(t)$, $n^{-j} = \sum_{k\ne j} n^k(t)$ and $\varphi^j = \varphi^j(t)$. Suppose platform $j$'s net fee satisfies the one-sided Logit form of the pricing formula (33),
--   $$t^j = c + \frac{1}{1-n^j} - 2\gamma n^j + \lambda\gamma\varphi^j n^j - \lambda\gamma\, n^{-j}.$$
--   Then $t^j$ is a best response: for every net fee $s \in \mathbb R$,
--   $$\pi^j(s, t^{-j}) \le \pi^j(t^j, t^{-j}).$$
--
--   The paper shows that, as a function of its own share, platform $j$'s profit has second derivative $-1/(n^j(1-n^j)^2) + 2\gamma(1-\lambda\varphi^j)$, and the bound (36) — the minimum of $1/(n(1-n)^2)$ over $(0,1)$ is $27/4$ — makes it non-positive. This is what turns a solution of the first-order condition into a Nash best response.
--
--   **Formalization Note** The paper states (33) for general demand and $S$ sides, and sketches its sufficiency in Appendix E.1.3 under the condition $\partial\varphi^j/\partial t^j \le 0$, which holds under Logit by (32). Here $S = 1$ and demand is Logit, so the markup is $1/(1-n^j)$. The bound $\gamma \le 27/8$ is the paper's Proposition 2′ bound (6.75 = 27/4 for $2\gamma$); together with $\lambda\varphi^j \in [0,1]$ it gives $2\gamma(1-\lambda\varphi^j) \le 27/4$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), pp. 46–47, Appendix E.1.3; p. 43, (36); p. 39, Proposition 11, (33)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropFee
theorem foc_best_response {J : ℕ} (w c γ lam : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hγ : γ ≤ 27 / 8) (t : Fin J → ℝ) (j : Fin J)
    (hfoc : t j = c + 1 / (1 - NetFeePlatform.Competition.demand w t j) - 2 * γ * NetFeePlatform.Competition.demand w t j
      + lam * γ * NetFeePlatform.Competition.diversion w t j * NetFeePlatform.Competition.demand w t j
      - lam * γ * ∑ k ∈ Finset.univ.erase j, NetFeePlatform.Competition.demand w t k) :
    ∀ s : ℝ, NetFeePlatform.Competition.profit w c γ lam (Function.update t j s) j ≤ NetFeePlatform.Competition.profit w c γ lam t j := by sorry
end NetFeePlatform.InteropFee
