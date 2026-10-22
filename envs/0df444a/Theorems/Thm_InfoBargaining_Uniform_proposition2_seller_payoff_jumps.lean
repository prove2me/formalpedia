-- Prove2me | Theorems.Thm_InfoBargaining_Uniform_proposition2_seller_payoff_jumps
-- name    : InfoBargaining.Uniform.proposition2_seller_payoff_jumps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:58:00.396394+00:00
-- url     : https://prove2.me/theorems/ec2ba85f-7282-44a4-bd51-c2f83b23acf1
-- title:
--   Proposition 2, p. 14 (uniform prior, linear cost) — the seller's payoff rises in θs but drops at 1 − θ̃; U*_s falls in c but jumps up at c_l; V*_s rises in c but drops at c_h
-- statement:
--   Consider the model with the uniform prior on $[0,1]$ and the linear information cost. The seller's bargaining power is $\theta_s=1-\theta_b$. Its equilibrium expected payoff is $U_s^*=\theta_sA(\alpha^*,c)$ when $c$ is a material cost and $V_s^*=c+\theta_sA(\alpha^*,c)$ when $c$ is an opportunity cost, where $\alpha^*$ is an optimal information level of the buyer. A *selection* is a choice $\sigma(t)\in\alpha^*$ of an optimal level for each parameter value $t\in(0,1)$. For every selection:
--
--   1. **Bargaining power.** Fix $c\in(0,1)$ and let $\tilde\theta$ be the threshold of Corollary 1 (i). Then $\theta_s\mapsto U_s^*$ and $\theta_s\mapsto V_s^*$ are nondecreasing on $(0,1-\tilde\theta)$ and on $(1-\tilde\theta,1)$. If $\tilde\theta<1$, both payoffs drop at $\theta_s=1-\tilde\theta$: there is $\varepsilon>0$ such that every value at $\theta'_s\in(1-\tilde\theta,1-\tilde\theta+\varepsilon)$ is strictly smaller than every value at $\theta_s\in(1-\tilde\theta-\varepsilon,1-\tilde\theta)$.
--   2. **Material cost.** Fix $\theta_b\in(0,1)$ and let $c_l\le 1/2\le c_h$ be thresholds of Corollary 1 (ii), i.e. for $c\in(0,1)$, $c_l<c<c_h$ exactly when $\theta_b[A(\bar\alpha,c)-A(\underline\alpha,c)]>\bar k$. Then $c\mapsto U_s^*$ is nonincreasing on $(0,c_l)$ and on $(c_l,1)$. If $c_l<c_h$, it jumps up at $c_l$: for some $\varepsilon>0$, every value at $c'\in(c_l,c_l+\varepsilon)$ strictly exceeds every value at $c\in(c_l-\varepsilon,c_l)$.
--   3. **Opportunity cost.** With the same $\theta_b$, $c_l$, $c_h$, the map $c\mapsto V_s^*$ is nondecreasing on $(0,c_h)$ and on $(c_h,1)$. If $c_l<c_h$, it drops at $c_h$: for some $\varepsilon>0$, every value at $c'\in(c_h,c_h+\varepsilon)$ is strictly smaller than every value at $c\in(c_h-\varepsilon,c_h)$.
--
--   The result shows that endogenous information gathering by the buyer can reverse the direct effect of a parameter on the seller: more bargaining power or a more valuable outside option can hurt the seller, and a higher production cost can help it.
--
--   **Formalization Note** The paper states Proposition 2 for four focal priors and works out only the uniform one; this statement is restricted to the uniform prior. "Increases … but may decrease discontinuously at $t_0$" is read as monotonicity on each side of $t_0$, open at $t_0$ (at a threshold both corners can be optimal; across the other cost threshold the payoff stays monotone), together with a strict one-sided jump whenever the threshold is interior ($\tilde\theta<1$, resp. $c_l<c_h$; in the remaining case the buyer never gathers information and there is no jump). The statement holds for every selection of optimal levels, so it does not depend on how ties are broken.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 14, Proposition 2; payoffs U*_s, V*_s p. 12; Corollary 1 p. 13

import Mathlib
import Definitions.Def_InfoBargaining_Uniform_Setting

namespace InfoBargaining.Uniform

theorem proposition2_seller_payoff_jumps (M : Model) :
    -- (i) payoffs in the seller's bargaining power θs = 1 − θb, jump down at θs = 1 − θ̃
    (∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ σ : ℝ → ℝ,
      (∀ θs ∈ Set.Ioo (0:ℝ) 1, σ θs ∈ M.optSet (1 - θs) c) →
      MonotoneOn (fun θs => θs * A (σ θs) c) (Set.Ioo 0 (1 - M.thetaTilde c)) ∧
      MonotoneOn (fun θs => θs * A (σ θs) c) (Set.Ioo (1 - M.thetaTilde c) 1) ∧
      MonotoneOn (fun θs => c + θs * A (σ θs) c) (Set.Ioo 0 (1 - M.thetaTilde c)) ∧
      MonotoneOn (fun θs => c + θs * A (σ θs) c) (Set.Ioo (1 - M.thetaTilde c) 1) ∧
      (M.thetaTilde c < 1 → ∃ ε > 0, ∀ θ ∈ Set.Ioo (0:ℝ) 1, ∀ θ' ∈ Set.Ioo (0:ℝ) 1,
        1 - M.thetaTilde c - ε < θ → θ < 1 - M.thetaTilde c →
        1 - M.thetaTilde c < θ' → θ' < 1 - M.thetaTilde c + ε →
        θ' * A (σ θ') c < θ * A (σ θ) c ∧ c + θ' * A (σ θ') c < c + θ * A (σ θ) c)) ∧
    -- (ii) U*_s in the material cost c, jump up at c = c_l
    (∀ θb ∈ Set.Ioo (0:ℝ) 1, ∀ cl ch : ℝ, cl ≤ 1 / 2 → 1 / 2 ≤ ch →
      (∀ c ∈ Set.Ioo (0:ℝ) 1, (cl < c ∧ c < ch ↔ M.kbar < θb * M.gain c)) →
      ∀ σ : ℝ → ℝ, (∀ c ∈ Set.Ioo (0:ℝ) 1, σ c ∈ M.optSet θb c) →
      AntitoneOn (fun c => (1 - θb) * A (σ c) c) (Set.Ioo 0 cl) ∧
      AntitoneOn (fun c => (1 - θb) * A (σ c) c) (Set.Ioo cl 1) ∧
      (cl < ch → ∃ ε > 0, ∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ c' ∈ Set.Ioo (0:ℝ) 1,
        cl - ε < c → c < cl → cl < c' → c' < cl + ε →
        (1 - θb) * A (σ c) c < (1 - θb) * A (σ c') c')) ∧
    -- (iii) V*_s in the opportunity cost c, jump down at c = c_h
    (∀ θb ∈ Set.Ioo (0:ℝ) 1, ∀ cl ch : ℝ, cl ≤ 1 / 2 → 1 / 2 ≤ ch →
      (∀ c ∈ Set.Ioo (0:ℝ) 1, (cl < c ∧ c < ch ↔ M.kbar < θb * M.gain c)) →
      ∀ σ : ℝ → ℝ, (∀ c ∈ Set.Ioo (0:ℝ) 1, σ c ∈ M.optSet θb c) →
      MonotoneOn (fun c => c + (1 - θb) * A (σ c) c) (Set.Ioo 0 ch) ∧
      MonotoneOn (fun c => c + (1 - θb) * A (σ c) c) (Set.Ioo ch 1) ∧
      (cl < ch → ∃ ε > 0, ∀ c ∈ Set.Ioo (0:ℝ) 1, ∀ c' ∈ Set.Ioo (0:ℝ) 1,
        ch - ε < c → c < ch → ch < c' → c' < ch + ε →
        c' + (1 - θb) * A (σ c') c' < c + (1 - θb) * A (σ c) c)) := by sorry

end InfoBargaining.Uniform
