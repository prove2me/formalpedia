-- Prove2me | Theorems.Thm_MarkovEntanglementExact_Supplement_atv_entanglement_bound_multi
-- name    : MarkovEntanglementExact.Supplement.atv_entanglement_bound_multi
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:53:44.052664+00:00
-- url     : https://prove2.me/theorems/5df045c6-707a-48fd-a4ef-8cc742e5670f
-- title:
--   Theorem 8 — for N agents, the agent-wise TV measures of entanglement bound the local-transition bias and the entry-wise value-decomposition error
-- statement:
--   Let $P$ be a transition matrix on $S_1\times\dots\times S_N$, the joint state-action pairs of $N$ agents, $\mu$ a probability distribution on it with positive agent marginals, and $P^\pi_i$ the local transition of agent $i$ (Appendix H). The measure of entanglement of agent $i$ with respect to the agent-wise total variation distance is
--   $$E_i(P)=\min_{P_i}\max_{x}\tfrac12\sum_{t}\Big|\sum_{y:\,y_i=t}P(x,y)-P_i(x_i,t)\Big|,$$
--   the minimum over transition matrices $P_i$ on agent $i$'s pairs (Eq. (8) under the ATV distance).
--
--   1. For every agent $i$ and every optimal $P_i$,
--   $$\|P^\pi_i-P_i\|_\infty\le2E_i(P),$$
--   where $\|M\|_\infty=\max_s\sum_t|M(s,t)|$ is the induced $\ell_\infty$ matrix norm.
--   2. For $0\le\gamma<1$ and local rewards with $|r_i|\le r^i_{\max}$,
--   $$\Big\|Q(s,a)-\sum_{i=1}^NQ_i(s_i,a_i)\Big\|_\infty\le\frac{4\gamma\sum_{i=1}^NE_i(P)\,r^i_{\max}}{(1-\gamma)^2},$$
--   with $Q$ the Q-value of $P$ for $\sum_ir_i$ and $Q_i$ that of $P^\pi_i$ for $r_i$.
--
--   This generalizes Theorem 4 to $N$ agents.
--
--   **Formalization Note** $E_i$ is the published `agentEntanglementWith i (agentTVDistN i)`. The matrix-norm bound is stated row by row.
--
--   Differences from the source:
--   - generalization: P^π_{1:N}, the transition matrix of an N-agent MDP under π, with |S_i| = |S| and |A_i| = |A| → any transition matrix P on the product of arbitrary finite types S i of agent state-action pairs, any N; reason: the proof uses only that P is a transition matrix; P^π_{1:N} is an instance, so the Lean statement specializes to the source
--   - generalization: µ^π_{1:N} (Appendix H's ρ^π_{1:N}) the stationary distribution of a unichain system → µ any distribution with positive agent marginals (IsOccupancyN), not assumed stationary or unique; reason: the proof uses only the local transition's defining identity; the paper's µ is an instance
--   - reading: ‖P^π_i − P_i‖_∞ ≤ 2_iE(P^π_{1:N}) → ≤ 2 · E_i(P); reason: misplaced subscript: Theorems 4, 6, 9 and "w.r.t ATV distance" with E_i(P^π_{1:N}) give 2E_i
--   - reading: ρ^π_{1:N}(s_{−i}, a_{−i} | s_i, a_i) in Appendix H's local transition → the conditional of the occupancy µ; reason: Appendix H uses ρ for the occupancy µ of §2 and Eq. (2)
--   - encoding: the local transition with the conditional ρ(s_{−i}, a_{−i} | s_i, a_i) → IsLocalTransitionN, multiplied by the positive marginal; reason: equivalent when the marginal is positive
--   - encoding: ‖M‖_∞ = sup_{‖x‖∞=1} ‖Mx‖_∞ (§1.3) → Σ_t |M(s, t)| ≤ c for every row s; reason: the induced ℓ∞ norm is the maximum absolute row sum
--   - encoding: E_i as Eq. (8) under the ATV distance, min over P ∈ P_SEP → min over transition matrices P_i of the agent-wise TV distance (published agentEntanglementWith i (agentTVDistN i)); reason: the N-agent form of Eq. (5): the ATV distance to a separable matrix depends only on its i-th part Σ_j x_j P^(j)_i (Lemma 6)
--   - encoding: Q-values Q = (I − γP)^{-1} r → Q-values as solutions of the Bellman equation (IsBellmanQ); reason: for 0 ≤ γ < 1 the Bellman equation has exactly the solution (I − γP)^{-1} r
--   - encoding: "where P_i is the optimal solution of Eq. (8)" → the bound for every optimal solution, quantified universally; reason: the paper does not fix one minimizer; the minimum is attained, so the hypothesis is satisfiable
--   - encoding: ‖v‖_∞ ≤ c for the vector of decomposition errors → |v(p)| ≤ c at every joint pair p; reason: the same statement
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 8, p.40 (with Definition 14 and Appendix H's local transition, p.40)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_markov_entanglement_multi_atv
import Definitions.Def_MarkovEntanglementExact_Supplement_IsOccupancyN

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- **Theorem 8** (`N` agents, agent-wise total variation). Let `P` be a transition matrix on the
joint state-action pairs of `N` agents, `μ` an occupancy whose agent marginals are positive,
`P^π_i` the local transition of agent `i` (Appendix H), and `E_i(P)` the measure of Eq. (8) under
the agent-wise total variation distance.

1. For every agent `i` and every optimal `P_i`: `‖P^π_i − P_i‖_∞ ≤ 2E_i(P)`, where `‖·‖_∞` is the
   induced matrix norm (maximum absolute row sum).
2. For `0 ≤ γ < 1` and local rewards with `|r_i| ≤ r^i_max`, at every joint pair
   `|Q(s, a) − Σ_i Q_i(s_i, a_i)| ≤ 4γ(Σ_i E_i(P) r^i_max)/(1 − γ)²`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 8, p.40, with
Definition 14 and the local transition of Appendix H, p.40, Eq. (8), p.21, and Definition 5,
p.15.

**Formalization Note.** The printed bound `2_iE(P^π_{1:N})` is read as `2E_i(P^π_{1:N})`
(misplaced subscript), and Appendix H's `ρ^π_{1:N}` as the occupancy `μ`. `E_i` is the published
`agentEntanglementWith i (agentTVDistN i)` (minimum over local transition matrices `P_i` of the
agent-wise TV distance, the `N`-agent form of Eq. (5)). `‖P^π_i − P_i‖_∞ ≤ c` is stated row by
row. `P` is any transition matrix on `Joint S`, `μ` need not be stationary, Q-values are Bellman
solutions, and the vector `‖·‖∞` bound is stated at every joint pair. -/
theorem atv_entanglement_bound_multi
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsOccupancyN μ)
    (Pπ : ∀ i, Matrix (S i) (S i) ℝ) (hPπ : ∀ i, IsLocalTransitionN i P μ (Pπ i)) :
    (∀ (i : Fin N) (Popt : Matrix (S i) (S i) ℝ), IsTransitionMatrix Popt →
        agentTVDistN i P Popt = agentEntanglementWith i (agentTVDistN i) P →
        ∀ s : S i, ∑ t, |Pπ i s t - Popt s t| ≤
          2 * agentEntanglementWith i (agentTVDistN i) P) ∧
    ∀ (γ : ℝ), 0 ≤ γ → γ < 1 →
      ∀ (r : ∀ i, S i → ℝ) (rmax : Fin N → ℝ), (∀ i s, |r i s| ≤ rmax i) →
        ∀ (Q : Joint S → ℝ) (Qloc : ∀ i, S i → ℝ),
          IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q →
          (∀ i, IsBellmanQ (Pπ i) (r i) γ (Qloc i)) →
          ∀ p : Joint S, |Q p - ∑ i, Qloc i (p i)| ≤
            4 * γ * (∑ i, agentEntanglementWith i (agentTVDistN i) P * rmax i) /
              (1 - γ) ^ 2 := by sorry

end MarkovEntanglementExact.Supplement
