-- Prove2me | Theorems.Thm_NetFeePlatform_InteropDominance_interop_equivalence
-- name    : NetFeePlatform.InteropDominance.interop_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:10.897745+00:00
-- url     : https://prove2.me/theorems/08588700-6074-4c6a-a566-cf0dbb2188d0
-- title:
--   §6.1, p. 24 — a duopoly with cost c, externality γ and interoperability λ has the equilibria of one with cost c − γλ, externality γ(1 − λ) and none
-- statement:
--   Consider the Logit duopoly without outside option. For every marginal cost $c$, network-interaction value $\gamma$ and interoperability $\lambda$, a fee profile $t$ is a Nash equilibrium in net fees of the market $(c,\gamma,\lambda)$ if and only if it is a Nash equilibrium of the market with
--
--   $$\tilde c=c-\gamma\lambda,\qquad \tilde\gamma=\gamma(1-\lambda),\qquad\text{and no interoperability}.$$
--
--   This makes precise the paper's observation that raising interoperability acts like lowering the network externality: in a duopoly without outside option the two markets have the same profit functions.
--
--   **Formalization Note** The statement is the equivalence of the two equilibrium sets for every fee profile, with no range imposed on $c,\gamma,\lambda$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 24, §6.1

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropDominance

theorem interop_equivalence (c γ lam : ℝ) (t : Fin 2 → ℝ) :
    NetFeePlatform.Competition.IsEquilibrium 0 c γ lam t ↔ NetFeePlatform.Competition.IsEquilibrium 0 (c - γ * lam) (γ * (1 - lam)) 0 t := by sorry

end NetFeePlatform.InteropDominance
