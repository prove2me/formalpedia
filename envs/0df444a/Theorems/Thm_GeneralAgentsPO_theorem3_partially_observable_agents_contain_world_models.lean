-- Prove2me | Theorems.Thm_GeneralAgentsPO_theorem3_partially_observable_agents_contain_world_models
-- name    : GeneralAgentsPO.theorem3_partially_observable_agents_contain_world_models
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:20:59.686146+00:00
-- url     : https://prove2.me/theorems/8e2f5cac-c30b-45fa-881c-ea76a06c2dbb
-- title:
--   Theorem 3 (as proved): stochastic $\delta$-optimal agents contain world models under partial observability
-- statement:
--   Let $\mathcal S,\mathcal A,O$ be finite sets with $|\mathcal A|\ge2$. Fix $s,s'\in\mathcal S$, $a\in\mathcal A$, an integer $n\ge1$ and $\delta<\tfrac12$, and put $L=\log\frac{2(1-\delta)}{1-2\delta}$. There is an estimator $\hat P$ with the following property. It receives only the agent's observable first-step behaviour: for every goal $\psi$, start state $x$ and action $c$, the probability $q_\psi(x,c)=\sum_{o}\Omega(o\mid x)\Pr(\pi_\psi(o)=c)$ that the agent, started in $x$, takes $c$ as its first action. For every partially observable cMDP $(\mathcal S,\mathcal A,P,O,\Omega)$ whose cMDP is communicating, and every goal-conditioned observation-based policy $\pi$ that is $(2n+1)$-th-degree $\delta$-optimal for it,
--
--   $$\big|\hat P(q)-P(s'\mid s,a)\big|\le\sqrt{\frac{2P(s'\mid s,a)\big(1-P(s'\mid s,a)\big)}{n}L}+\frac{2L}{3n}+\frac1n.$$
--
--   Even an agent that cannot see the state, if it is nearly optimal for goals phrased in terms of states, determines the transition probabilities.
--
--   **Formalization Note** The paper states that Theorem 2 "continues to hold" for observation-based policies, with the estimator obtained "by querying the policy". If the estimator may look only at the policy as a function of observation histories, the statement is false. Let each of two environments with the same states have state-revealing observations, the first emitting $o^1_x$ in state $x$ and the second $o^2_x$, and let them have $P(s'\mid s,a)=0.1$ and $0.9$. Take $\delta\in(0,\frac12)$ and $n$ large enough that the bound is below $0.4$. A single policy that, after a first observation $o^i_x$, plays a nearly optimal policy for environment $i$ from $x$ is $\delta$-optimal in both, so an estimator that sees only the policy returns the same value in both. The proof uses only the probabilities of the agent's first action from a start state inside the environment, $\sum_o\Omega(o\mid s_0)\Pr(\pi_{\xi}(o)=c)$, which is what querying the agent as a black box gives. The estimator receives exactly these numbers, for all goals, start states and actions, and nothing else; in particular it does not receive $\Omega$ or $P$. The hypotheses $|\mathcal A|\ge2$ and $n\ge1$ are added as in Theorem 2, and $O$ is finite.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 4.2, Theorem 3, p. 12; proof pp. 12-14

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem theorem3_partially_observable_agents_contain_world_models {S A O : Type*} [Fintype S]
    [DecidableEq S] [Fintype A] [DecidableEq A] [Fintype O] (hA : 2 ≤ Fintype.card A)
    (s s' : S) (a : A) (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : δ < 1 / 2) :
    ∃ est : (CompGoal S A → S → A → ℝ) → ℝ, ∀ M : POCMP S A O, M.toCMP.IsCommunicating →
      ∀ π : GCStochPolicy S O A, IsObsDeltaOptimal M δ (PsiDepth (2 * n + 1)) π →
        |est (fun ψ x c => ∑ o, M.obs x o * (π ψ).act [] o c) - M.P s a s'| ≤
          Real.sqrt (2 * M.P s a s' * (1 - M.P s a s') / n *
              Real.log (2 * (1 - δ) / (1 - 2 * δ))) +
            2 * Real.log (2 * (1 - δ) / (1 - 2 * δ)) / (3 * n) + 1 / n := by sorry

end GeneralAgentsPO
