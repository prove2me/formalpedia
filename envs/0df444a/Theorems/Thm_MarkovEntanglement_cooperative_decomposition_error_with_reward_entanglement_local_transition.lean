-- Prove2me | Theorems.Thm_MarkovEntanglement_cooperative_decomposition_error_with_reward_entanglement_local_transition
-- name    : MarkovEntanglement.cooperative_decomposition_error_with_reward_entanglement_local_transition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T14:40:46.126666+00:00
-- url     : https://prove2.me/theorems/f23d4fcd-7736-4c2f-84a7-41f7c01159a8
-- title:
--   Shared rewards add a reward-entanglement term to the error against the marginalized local value functions
-- statement:
--   **Proposition 4 (Chen and Peng, p. 42), $N$-agent form, stated with $Q^\pi_i$ the value function of the marginalized local chain.**
--
--   Consider a fully cooperative $N$-agent Markov system $\mathcal{M}_{1:N}$ and a policy $\pi$, with discount factor $\gamma \in [0,1)$, occupancy measure $\mu^\pi_{1:N}$ strictly positive and stationary for $P^\pi_{1:N}$, and a shared reward $r$ on the joint space. Let $r_i$ be local rewards attaining the measure of reward entanglement $\mathcal{E}_r(r) = \inf_{r_{1:N}} \bigl\| r - \sum_i r_i \bigr\|_{\mu^\pi_{1:N}}$, each bounded by $r^i_{\max}$.
--
--   For each agent $i$, let $P^\pi_i$ denote the local (marginalized) transition induced by $P^\pi_{1:N}$ and $\mu^\pi_{1:N}$ through Eq. (2), and let $Q^\pi_i$ be the Q-value of $P^\pi_i$ under $r_i$. Let $\mathcal{E}_i(P^\pi_{1:N})$ be the measure of Markov entanglement of agent $i$ with respect to the $\mu^\pi_{1:N}$-weighted agent-wise total variation distance. Then
--
--   $$\Bigl\| \, Q^\pi_{1:N}(s,a) - \sum_{i=1}^{N} Q^\pi_i(s_i,a_i) \, \Bigr\|_{\mu^\pi_{1:N}} \;\le\; \frac{\mathcal{E}_r(r)}{1-\gamma} \;+\; \frac{4\gamma \sum_{i=1}^{N} \mathcal{E}_i\bigl(P^\pi_{1:N}\bigr)\, r^i_{\max}}{(1-\gamma)^2}.$$
--
--   ## Notes
--
--   Here $Q^\pi_i$ solves the Bellman equation of $P^\pi_i$, the chain of Eq. (2), which is the $Q^\pi_i$ appearing in the paper's statement. It is a different object from the Q-value of the entanglement-attaining $P_i$; the two chains are compared by the first part of Theorem 6.
--
--   A shared reward contributes an additive term $\mathcal{E}_r(r)/(1-\gamma)$, linear in the reward entanglement and carrying only one factor of $(1-\gamma)^{-1}$: a reward mismatch is paid once per step, whereas a transition mismatch compounds. Setting $\mathcal{E}_r(r) = 0$ recovers Theorem 6.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Proposition 4, p. 42, N-agent form; Theorem 6 proof legs (I) and (II), pp. 39-40; local transition Eq. (2)

import Mathlib
import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem cooperative_decomposition_error_with_reward_entanglement_local_transition
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : Joint S → ℝ) (rl : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl Ptrue : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |rl i s| ≤ rmax i)
    (hrl : muNorm μ (fun p => r p - ∑ i, rl i (p i)) = rewardEntanglement μ r)
    (hQ : IsBellmanQ P r γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, muAgentTVDistN i μ P (Pl i) = entanglementN i μ P)
    (hPtrue : ∀ i, IsTransitionMatrix (Ptrue i))
    (htrue : ∀ i, IsLocalTransitionN i P μ (Ptrue i))
    (hQi : ∀ i, IsBellmanQ (Ptrue i) (rl i) γ (Qi i)) :
    muNorm μ (fun p => Q p - ∑ i, Qi i (p i))
      ≤ rewardEntanglement μ r / (1 - γ)
        + 4 * γ * (∑ i, entanglementN i μ P * rmax i) / (1 - γ) ^ 2 := by
  sorry

end MarkovEntanglement
