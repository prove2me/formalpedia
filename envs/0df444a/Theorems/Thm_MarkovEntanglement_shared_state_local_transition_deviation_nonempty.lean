-- Prove2me | Theorems.Thm_MarkovEntanglement_shared_state_local_transition_deviation_nonempty
-- name    : MarkovEntanglement.shared_state_local_transition_deviation_nonempty
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T23:48:40.14083+00:00
-- url     : https://prove2.me/theorems/15e26bfc-08b3-4c14-bcff-2d3965b30986
-- title:
--   Entanglement bound with a shared global state
-- statement:
--   ## Statement
--
--   Consider an $N$-agent Markov system with a shared global coordinate, so that a joint state is a pair $p=(p_1,z)$ of a local state-action for each agent together with a common coordinate $z$, and assume every agent's local space is nonempty. Fix an agent $i$ and write
--   $$m_i(p,t) \;=\; \sum_{q\,:\,(q_1)_i=t_1,\ q_2=t_2} P(p,q), \qquad t \in S_i \times Z,$$
--   for the joint transition marginalised onto agent $i$'s coordinate together with the shared one.
--
--   Suppose the marginal is *exactly local*, i.e. there is a matrix $P^{\mathrm{true}}$ on $S_i \times Z$ with
--   $$m_i(p,t) \;=\; P^{\mathrm{true}}\bigl((p_1)_i, p_2;\, t\bigr) \qquad\text{for all } p,\,t,$$
--   and suppose a candidate local transition $P_i$ approximates the same marginal entrywise,
--   $$\bigl| m_i(p,t) - P_i\bigl((p_1)_i, p_2;\, t\bigr) \bigr| \;\le\; \mathcal{E} \qquad\text{for all } p,\,t .$$
--   Then $P^{\mathrm{true}}$ and $P_i$ are uniformly close:
--   $$\bigl\| P^{\mathrm{true}} - P_i \bigr\|_\infty \;\le\; 2\,\mathcal{E}.$$
--
--   ## Notes
--
--   The shared-state analogue of the local transition bound, and the step that carries the entanglement machinery over to systems with a common observable coordinate. Together with the exact-decomposition result for separable shared-state systems it gives the shared-state theory its two halves: no error when the system is separable, a controlled error when it is not.
--
--   **Why every local space must be nonempty.** This hypothesis is not decoration. Both assumptions above quantify over joint states $p$, while the conclusion quantifies over $S_i \times Z$. If some *other* agent $j \neq i$ has an empty state space, the joint space is empty, both hypotheses hold vacuously for arbitrary $P^{\mathrm{true}}$ and arbitrary $\mathcal{E}$, and yet $S_i \times Z$ can be nonempty — so the conclusion fails outright. A version of this statement without the nonemptiness assumption is refutable: take two agents with $S_0$ empty and $S_1$, $Z$ singletons, $P^{\mathrm{true}} \equiv 5$, $P_i \equiv 1$ and $\mathcal{E}=0$.
--
--   With every $S_j$ nonempty the proof is immediate, and this is what nonemptiness buys: given any $s \in S_i \times Z$ one can *realise* it, by taking an arbitrary local state for each agent and overwriting agent $i$'s with $s$'s first component. Evaluating both hypotheses at that joint state gives $|P^{\mathrm{true}}(s,t) - P_i(s,t)| \le \mathcal{E}$ directly, so the stated constant $2$ is slack here — it is inherited from the product-state versions, where $\mathcal{E}$ measures a total variation distance carrying a factor $\tfrac12$, whereas here it already bounds individual entries.
--
--   Note also that the $\mu$-weighted siblings of this statement need no such hypothesis: there a strictly positive occupancy measure with total mass one already forces the joint space to be inhabited.
--
--   Search terms: marginalised transition with shared state, agent-wise total variation, global coordinate multi-agent MDP, entrywise transition bound, weakly coupled MDP with common state.
-- source:
--   Shuze Chen and Tianyi Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Theorem 9, p. 46

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglement

theorem shared_state_local_transition_deviation_nonempty
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, Nonempty (S i)]
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (hP : IsTransitionMatrix P)
    (i : Fin N) (E : ℝ)
    (Pi Ptrue : Matrix (S i × Z) (S i × Z) ℝ) (hPi : IsTransitionMatrix Pi)
    (htrue : ∀ p t, marginalZ i P p t = Ptrue (p.1 i, p.2) t)
    (hE : ∀ p t, |marginalZ i P p t - Pi (p.1 i, p.2) t| ≤ E) :
    ∀ s t, |Ptrue s t - Pi s t| ≤ 2 * E := by
  sorry

end MarkovEntanglement
