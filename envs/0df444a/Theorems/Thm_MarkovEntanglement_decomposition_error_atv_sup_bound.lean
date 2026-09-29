-- Prove2me | Theorems.Thm_MarkovEntanglement_decomposition_error_atv_sup_bound
-- name    : MarkovEntanglement.decomposition_error_atv_sup_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-07T16:13:24.46022+00:00
-- url     : https://prove2.me/theorems/2aacfd24-69a1-46ec-bb60-e8909c0e02de
-- title:
--   Entrywise bound on the value decomposition error under the ATV measure of entanglement
-- statement:
--   **Theorem 8, second part (Chen and Peng, p. 40), the entrywise value-decomposition error.**
--
--   Consider an $N$-agent MDP with joint transition $P^\pi_{1:N}$, occupancy measure $\mu$ strictly positive and stationary, discount factor $\gamma \in [0,1)$, and local rewards $r_i$ bounded by $r^{\max}_i$. Let $Q^\pi_{1:N}$ be the Q-value of the joint system under the additive reward $\sum_i r_i$, and for each agent let $P_i$ attain the measure of Markov entanglement **with respect to the unweighted agent-wise total variation distance**, with $Q^\pi_i$ the Q-value of that local chain.
--
--   Then the error of decomposing the global Q-value into the sum of local Q-values is bounded at every joint state-action pair:
--   $$\Big\|Q^\pi_{1:N} - \sum_{i=1}^N Q^\pi_i\Big\|_\infty \le \frac{4\gamma\left(\sum_{i=1}^N \mathcal{E}_i(P^\pi_{1:N})\, r^{\max}_i\right)}{(1-\gamma)^2}.$$
--
--   This is the $N$-agent generalization of Theorem 4, whose two-agent case is already proved on the platform. The route follows the source: the first part of Theorem 8 controls each local transition uniformly, the resolvent identity (Lemma 1) converts the resulting inverse error into a transition perturbation, and a Bellman fixed point on a finite state space satisfies $\|Q_i\|_\infty \le r^{\max}_i/(1-\gamma)$, which produces the factor $4\gamma/(1-\gamma)^2$.
--
--   As in the first part, the supremum-based measure is essential: with the $\mu$-weighted measure the entrywise conclusion fails, and the correct statement on that row is the goal theorem, whose error is measured in $\|\cdot\|_\mu$.
-- source:
--   Shuze Chen and Tianyi Peng, 'Multi-agent Markov Entanglement', arXiv:2506.02385v3, Theorem 8, p. 40 (second part), with the distance/norm pairing of Table 1, p. 20

import Mathlib
import Definitions.Def_markov_entanglement_multi_atv

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem decomposition_error_atv_sup_bound
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (μ : Joint S → ℝ) (γ : ℝ) (rmax : Fin N → ℝ)
    (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ)
    (Pl : ∀ i, Matrix (S i) (S i) ℝ) (Qi : ∀ i, S i → ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hP : IsTransitionMatrix P)
    (hμ : IsPositiveDist μ) (hstat : IsStationary P μ)
    (hr : ∀ i s, |r i s| ≤ rmax i)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q)
    (hPl : ∀ i, IsTransitionMatrix (Pl i))
    (hopt : ∀ i, agentTVDistN i P (Pl i) = agentEntanglementWith i (agentTVDistN i) P)
    (hQi : ∀ i, IsBellmanQ (Pl i) (r i) γ (Qi i)) (p : Joint S) :
    |Q p - ∑ i, Qi i (p i)|
      ≤ 4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) / (1 - γ) ^ 2 := by
  sorry

end MarkovEntanglement
