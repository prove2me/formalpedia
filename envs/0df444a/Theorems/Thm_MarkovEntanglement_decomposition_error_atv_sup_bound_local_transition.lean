-- Prove2me | Theorems.Thm_MarkovEntanglement_decomposition_error_atv_sup_bound_local_transition
-- name    : MarkovEntanglement.decomposition_error_atv_sup_bound_local_transition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T01:25:32.045181+00:00
-- url     : https://prove2.me/theorems/61513581-a67b-4d23-bde6-057c7eb028a8
-- title:
--   Entrywise decomposition error against the marginalized local value functions under the ATV measure
-- statement:
--   **Theorem 8, second part (Chen and Peng, p. 40), stated with $Q^\pi_i$ the value function of the marginalized local chain.**
--
--   Consider an $N$-agent MDP $\mathcal{M}_{1:N}$ and a policy $\pi$, with discount factor $\gamma \in [0,1)$, local rewards bounded by $r^i_{\max}$, and occupancy measure $\mu^\pi_{1:N}$ strictly positive and stationary for $P^\pi_{1:N}$.
--
--   For each agent $i$, let $P^\pi_i$ denote the local (marginalized) transition induced by $P^\pi_{1:N}$ and $\mu^\pi_{1:N}$ through Eq. (2), and let $Q^\pi_i$ be the Q-value of $P^\pi_i$ under the local reward $r_i$. Let $\mathcal{E}_i(P^\pi_{1:N})$ be the measure of Markov entanglement of agent $i$ with respect to the **unweighted** agent-wise total variation distance, attained at the local transition $P_i$. Then the decomposition error is bounded at every joint state-action pair:
--
--   $$\Bigl\| \, Q^\pi_{1:N}(s,a) - \sum_{i=1}^{N} Q^\pi_i(s_i,a_i) \, \Bigr\|_\infty \;\le\; \frac{4\gamma \sum_{i=1}^{N} \mathcal{E}_i\bigl(P^\pi_{1:N}\bigr)\, r^i_{\max}}{(1-\gamma)^2}.$$
--
--   ## Notes
--
--   Here $Q^\pi_i$ solves the Bellman equation of $P^\pi_i$, the chain of Eq. (2), which is the $Q^\pi_i$ appearing in the paper's statement. It is a different object from the Q-value of the entanglement-attaining $P_i$; the two chains are compared by the first part of Theorem 8.
--
--   The unweighted distance is paired with $\|\cdot\|_\infty$, as in Table 1, p. 20. Strict positivity of $\mu^\pi_{1:N}$ is used only to give every local state-action pair a positive marginal, which is what turns the conditional average defining $P^\pi_i$ into a uniform bound.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Theorem 8, p. 40 (second part), with the distance/norm pairing of Table 1, p. 20; local transition Eq. (2)

import Mathlib
import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem decomposition_error_atv_sup_bound_local_transition
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl Ptrue : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |r i s| ≤ rmax i)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, agentTVDistN i P (Pl i) = agentEntanglementWith i (agentTVDistN i) P)
    (hPtrue : ∀ i, IsTransitionMatrix (Ptrue i))
    (htrue : ∀ i, IsLocalTransitionN i P μ (Ptrue i))
    (hQi : ∀ i, IsBellmanQ (Ptrue i) (r i) γ (Qi i)) (p : Joint S) :
    |Q p - ∑ i, Qi i (p i)|
      ≤ 4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ) ^ 2 := by
  sorry

end MarkovEntanglement
