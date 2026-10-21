-- Prove2me | Theorems.Thm_InfoBargaining_Uniform_corollary1_ii_threshold_cost
-- name    : InfoBargaining.Uniform.corollary1_ii_threshold_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:47.52328+00:00
-- url     : https://prove2.me/theorems/fbf0f26c-989f-4fee-80a5-7e5d7d35fd9c
-- title:
--   Corollary 1 (ii), p. 13 — there are c_l ≤ û ≤ c_h with α* = α̲ for c ≤ c_l or c ≥ c_h and α* = ᾱ for c_l < c < c_h
-- statement:
--   Under the uniform prior (mean $\hat u=1/2$) and the linear information cost, fix the buyer's bargaining power $\theta_b\in(0,1)$. There exist thresholds $c_l\le 1/2\le c_h$ such that for every seller cost $c\in(0,1)$, with $\alpha^*$ the set of optimal information levels:
--
--   1. if $c\le c_l$ or $c\ge c_h$, minimal information is optimal: $\underline\alpha\in\alpha^*$;
--   2. if $c<c_l$ or $c>c_h$, it is the only optimum: $\alpha^*=\{\underline\alpha\}$;
--   3. if $c_l<c<c_h$, maximal information is the only optimum: $\alpha^*=\{\bar\alpha\}$.
--
--   The buyer gathers information only when the seller's cost lies in an intermediate range around the prior mean, where trade is most uncertain. The jumps of $\alpha^*$ at $c_l$ and $c_h$ drive Proposition 2 (ii) and (iii).
--
--   **Formalization Note** "$\alpha^*=\underline\alpha$ for $c\le c_l$ or $c\ge c_h$" is items 1 and 2: at a threshold both corners can be optimal and the paper selects $\underline\alpha$. When the buyer never gathers information, $c_l=c_h=1/2$ is allowed. Restricted to the uniform prior.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 13, Corollary 1 (ii); proof p. 30

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

namespace InfoBargaining.Uniform

theorem corollary1_ii_threshold_cost (M : Model) (θb : ℝ) (hθb : θb ∈ Set.Ioo (0:ℝ) 1) :
    ∃ cl ch : ℝ, cl ≤ 1 / 2 ∧ 1 / 2 ≤ ch ∧
      ∀ c ∈ Set.Ioo (0:ℝ) 1,
        ((c ≤ cl ∨ ch ≤ c) → M.αlo ∈ M.optSet θb c) ∧
        ((c < cl ∨ ch < c) → M.optSet θb c = {M.αlo}) ∧
        (cl < c ∧ c < ch → M.optSet θb c = {M.αhi}) := by sorry

end InfoBargaining.Uniform
