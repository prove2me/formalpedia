-- Prove2me | Theorems.Thm_NetFeePlatform_InteropDominance_eq20
-- name    : NetFeePlatform.InteropDominance.eq20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:04.635671+00:00
-- url     : https://prove2.me/theorems/0accec6c-e59c-4aae-b9a4-71efdddac301
-- title:
--   §6.1, (20), p. 23 — every duopoly equilibrium under interoperability λ satisfies the net-fee formula (20)
-- statement:
--   Consider two platforms with Logit demand and no outside option, marginal cost $c$, network-interaction value $\gamma$ and interoperability $\lambda$, with profits $\pi^j=(t^j+\gamma n^j+\lambda\gamma n^{-j}-c)n^j$, where $n^{-j}=1-n^j$ is the other platform's share. If the fee profile $t$ is a Nash equilibrium in net fees, then each platform's net fee satisfies
--
--   $$t^j=c+\frac{1}{1-n^j}-2\gamma n^j-\gamma\lambda(1-n^j)+\gamma\lambda n^j\qquad(j=1,2).$$
--
--   This is the paper's equation (20), the duopoly case of the pricing formula (33) of Proposition 11. It is the necessary first-order condition of each platform's profit maximization.
--
--   **Formalization Note** No range is imposed on $c,\gamma,\lambda$: the first-order condition is necessary at any equilibrium. "Equilibrium" is the global Nash condition over all unilateral deviations $s\in\mathbb R$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 23, (20); p. 39, Proposition 11, (33)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropDominance

theorem eq20 (c γ lam : ℝ) (t : Fin 2 → ℝ) (ht : NetFeePlatform.Competition.IsEquilibrium 0 c γ lam t) :
    ∀ j, t j = c + 1 / (1 - NetFeePlatform.Competition.demand 0 t j) - 2 * γ * NetFeePlatform.Competition.demand 0 t j
      - γ * lam * (1 - NetFeePlatform.Competition.demand 0 t j) + γ * lam * NetFeePlatform.Competition.demand 0 t j := by sorry

end NetFeePlatform.InteropDominance
