-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_theorem1_agent_choice_inequalities
-- name    : GeneralAgentsWorldModels.theorem1_agent_choice_inequalities
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:38:30.306067+00:00
-- url     : https://prove2.me/theorems/e79b5645-2966-4063-91e8-51b0bfa94222
-- title:
--   Theorem 1 (proof, eqs. (39)-(40)): the first action of a bounded agent witnesses a binomial inequality
-- statement:
--   Let the environment satisfy Assumption 1 and let $\pi$ be a bounded goal-conditioned agent with failure rate $\delta<1$ for all goals in $\Psi_n$. Let $m$ satisfy $2m+1\le n$, let $s,s'$ be states, $a\ne b$ actions, $k\in\mathbb N$, $s_0$ a state, and $p=P_{ss'}(a)$. Let $\psi_{a,b}(k,m)=\psi_a(k,m)\vee\psi_b(k,m)$, where $\psi_a(k,m)$ asks the agent to take $a$ and then to achieve the transition $(s,a)\to s'$ at most $k$ times in $m$ attempts, and $\psi_b(k,m)$ asks it to take $b$ and then to achieve it more than $k$ times. Write $X\sim\mathrm{Bin}(m,p)$. Then the agent's first action $a_0=\pi(s_0;\psi_{a,b}(k,m))$ is $a$ or $b$, and
--
--   $$a_0=a\implies P_m(X\le k)\ge P_m(X>k)(1-\delta),\qquad a_0=b\implies P_m(X>k)\ge P_m(X\le k)(1-\delta).$$
--
--   **Formalization Note** $\psi_{a,b}(k,m)$ has depth $2m+1$, which is why $2m+1\le n$ is assumed. No condition $s\ne s'$ is imposed, as in the statement of Theorem 1; the binomial formula of Lemma 6 also holds for $s=s'$ (the successive visits to $(s,a)$ are i.i.d. trials by the strong Markov property).
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, proof of Theorem 1, eqs. (33)-(40), pp. 17-18

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem theorem1_agent_choice_inequalities {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (π : GCPolicy S A) (δ : ℝ) (hδ : δ < 1)
    (n m : ℕ) (hm : 2 * m + 1 ≤ n) (hπ : IsBoundedAgent M π δ n)
    (s s' : S) (a b : A) (hab : a ≠ b) (k : ℕ) (s₀ : S) :
    (π (abGoal a b s s' m k) [] s₀ = a ∨ π (abGoal a b s s' m k) [] s₀ = b) ∧
    (π (abGoal a b s s' m k) [] s₀ = a →
      binGE m (M.P s a s') (k + 1) * (1 - δ) ≤ binLE m (M.P s a s') k) ∧
    (π (abGoal a b s s' m k) [] s₀ = b →
      binLE m (M.P s a s') k * (1 - δ) ≤ binGE m (M.P s a s') (k + 1)) := by sorry

end GeneralAgentsWorldModels
