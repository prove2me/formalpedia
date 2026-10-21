-- Prove2me | Theorems.Thm_InfoBargaining_Uniform_corollary1_i_threshold_theta
-- name    : InfoBargaining.Uniform.corollary1_i_threshold_theta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:27.815153+00:00
-- url     : https://prove2.me/theorems/48e4bb03-f27b-4d73-8416-4b92968abdfc
-- title:
--   Corollary 1 (i), p. 13 — there is θ̃ ∈ (0, 1] with α* = α̲ for θb ≤ θ̃ and α* = ᾱ for θb > θ̃
-- statement:
--   Under the uniform prior and the linear information cost, fix the seller's cost $c\in(0,1)$ and let $\tilde\theta=\bar k/[A(\bar\alpha,c)-A(\underline\alpha,c)]$ when this gain exceeds $\bar k$, and $\tilde\theta=1$ otherwise. Then $\tilde\theta\in(0,1]$ and, for every buyer bargaining power $\theta_b\in(0,1)$, with $\alpha^*$ the set of optimal information levels:
--
--   1. if $\theta_b\le\tilde\theta$, minimal information is optimal: $\underline\alpha\in\alpha^*$;
--   2. if $\theta_b<\tilde\theta$, it is the only optimum: $\alpha^*=\{\underline\alpha\}$;
--   3. if $\theta_b>\tilde\theta$, maximal information is the only optimum: $\alpha^*=\{\bar\alpha\}$.
--
--   In words, the buyer acquires information only when its bargaining power is high enough to recover the information cost from its share of the surplus. The jump of $\alpha^*$ at $\theta_b=\tilde\theta$ drives the jump in the seller's payoff in Proposition 2 (i).
--
--   **Formalization Note** The paper's "$\alpha^*=\underline\alpha$ for $\theta_b\le\tilde\theta$" is items 1 and 2: at $\theta_b=\tilde\theta<1$ both corners are optimal and the paper selects $\underline\alpha$. Restricted to the uniform prior; the paper states the corollary for four priors but works out only this one.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 13, Corollary 1 (i); θ̃ from p. 30, proof of Corollary 1

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

namespace InfoBargaining.Uniform

theorem corollary1_i_threshold_theta (M : Model) (c : ℝ) (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    0 < M.thetaTilde c ∧ M.thetaTilde c ≤ 1 ∧
    ∀ θb ∈ Set.Ioo (0:ℝ) 1,
      (θb ≤ M.thetaTilde c → M.αlo ∈ M.optSet θb c) ∧
      (θb < M.thetaTilde c → M.optSet θb c = {M.αlo}) ∧
      (M.thetaTilde c < θb → M.optSet θb c = {M.αhi}) := by sorry

end InfoBargaining.Uniform
