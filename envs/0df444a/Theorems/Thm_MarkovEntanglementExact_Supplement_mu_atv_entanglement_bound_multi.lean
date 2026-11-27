-- Prove2me | Theorems.Thm_MarkovEntanglementExact_Supplement_mu_atv_entanglement_bound_multi
-- name    : MarkovEntanglementExact.Supplement.mu_atv_entanglement_bound_multi
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:53:11.14483+00:00
-- url     : https://prove2.me/theorems/9bd90518-57c4-45ef-90df-a54a432945b5
-- title:
--   Theorem 6 — for N agents, the µ-weighted agent-wise measures of entanglement bound the local-transition bias and the µ-norm value-decomposition error
-- statement:
--   Let $S_1,\dots,S_N$ be the finite sets of state-action pairs of $N$ agents and $P$ a transition matrix on $S_1\times\dots\times S_N$. Let $\mu$ be a stationary distribution of $P$ whose agent marginals $\mu_i$ are positive, and $P^\pi_i$ the local transition of agent $i$,
--   $$P^\pi_i(s_i',a_i'\mid s_i,a_i)=\sum_{s'_{-i},a'_{-i}}\ \sum_{s_{-i},a_{-i}}P(s',a'\mid s,a)\,\mu(s_{-i},a_{-i}\mid s_i,a_i).$$
--   For agent $i$, the $\mu$-weighted agent-wise distance is $\|P-P'\|_{\mu\text{-ATV}_i}=\frac12\sup_{\|x\|_\infty=1}\|(P-P')((e\otimes)^{i-1}x(\otimes e)^{N-i})\|_\mu$ (Definition 8) and $E_i(P)=\min_{P'\in\mathcal P_{\mathrm{SEP}}}\|P-P'\|_{\mu\text{-ATV}_i}$, the minimum over separable $N$-agent transition matrices $\sum_jx_jP^{(j)}_1\otimes\dots\otimes P^{(j)}_N$ (Definition 10, Eq. (8)).
--
--   1. For every agent $i$ and every optimal solution of $E_i(P)$, with $P_i=\sum_jx_jP^{(j)}_i$,
--   $$\|P^\pi_i-P_i\|_{\mu_i,\infty}\le2E_i(P).$$
--   2. For $0\le\gamma<1$ and local rewards with $|r_i|\le r^i_{\max}$, with $Q$ the Q-value of $P$ for the reward $\sum_ir_i(s_i,a_i)$ and $Q_i$ the Q-value of $P^\pi_i$ for $r_i$,
--   $$\Big\|Q(s,a)-\sum_{i=1}^NQ_i(s_i,a_i)\Big\|_\mu\le\frac{4\gamma\sum_{i=1}^NE_i(P)\,r^i_{\max}}{(1-\gamma)^2}.$$
--
--   This is the $N$-agent extension of Theorem 5; it is the bound applied to restless bandits through Theorem 7.
--
--   **Formalization Note** The joint space is the published `Joint S`, the local transition the published `IsLocalTransitionN`, and the measure `muEntanglementN` (Definition 8 with the supremum outside the sum, not the published `entanglementN`).
--
--   Differences from the source:
--   - generalization: P^π_{1:N}, the transition matrix of an N-agent MDP under π, with |S_i| = |S| and |A_i| = |A| → any transition matrix P on the product of arbitrary finite types S i of agent state-action pairs, any N; reason: the proof uses only that P is a transition matrix; P^π_{1:N} is an instance, so the Lean statement specializes to the source
--   - generalization: µ^π_{1:N} the unique stationary distribution of a unichain system → µ any stationary distribution of P with positive agent marginals (IsOccupancyN, IsStationary), uniqueness not assumed; reason: the proof uses stationarity but never uniqueness; the paper's µ is an instance
--   - reading: µ^π_i "the stationary distribution of the projected transition P^π_i" → µ_i the agent marginal marginalDist i μ; reason: Lemma 5 (stated for all agents, p.38) identifies it with the marginal; a stationary distribution of P^π_i need not be unique
--   - encoding: the local transition with the conditional µ(s_{−i}, a_{−i} | s_i, a_i) → IsLocalTransitionN, multiplied by the positive marginal µ_i; reason: equivalent when the marginal is positive, which IsOccupancyN assumes
--   - encoding: Q-values Q = (I − γP)^{-1} r → Q-values as solutions of the Bellman equation (IsBellmanQ); reason: for 0 ≤ γ < 1 the Bellman equation has exactly the solution (I − γP)^{-1} r
--   - encoding: "where P_i is the optimal solution of Eq. (8)" → the bound for every optimal solution, quantified universally; reason: the paper does not fix one minimizer; the minimum is attained, so the hypothesis is satisfiable
--   - encoding: P_i "the optimal solution of Eq. (8)" → P_i = Σ_j x_j P^(j)_i for an optimal separable transition matrix Σ_j x_j ⊗_i P^(j)_i; reason: the µ-weighted ATV distance to a separable matrix depends only on its i-th part (Lemma 6)
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 6, pp.21–22 (with Definitions 8, 10, Eq. (8), pp.19–21, and Appendix H, p.40)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_Supplement_IsOccupancyN
import Definitions.Def_MarkovEntanglementExact_Supplement_muInducedNorm
import Definitions.Def_MarkovEntanglementExact_Supplement_muATVDistN
import Definitions.Def_MarkovEntanglementExact_Supplement_muEntanglementN

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- **Theorem 6** (`N` agents, `μ`-weighted agent-wise total variation). Let `P` be a transition
matrix on the joint state-action pairs of `N` agents, `μ` a stationary distribution of `P` whose
agent marginals `μ_i` are positive, `P^π_i` the local transition of agent `i` (Appendix H), and
`E_i(P)` the measure of Eq. (8) under the `μ`-weighted agent-wise total variation distance.

1. For every agent `i` and every optimal solution `Q = Σ_j x_j P^(j)_1 ⊗ ⋯ ⊗ P^(j)_N ∈ P_SEP` of
   Eq. (8) for agent `i`, with `P_i = Σ_j x_j P^(j)_i`: `‖P^π_i − P_i‖_{μ_i,∞} ≤ 2E_i(P)`.
2. For `0 ≤ γ < 1` and local rewards with `|r_i| ≤ r^i_max`, the global Q-value `Q` of `P` for
   `Σ_i r_i(s_i, a_i)` and the local Q-values `Q_i` of `P^π_i` satisfy
   `‖Q(s, a) − Σ_i Q_i(s_i, a_i)‖_μ ≤ 4γ(Σ_i E_i(P) r^i_max)/(1 − γ)²`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 6, pp.21–22,
with Definition 10 and Eq. (8), p.21, Definition 8, p.19, and the local transition of
Appendix H, p.40.

**Formalization Note.** Agents have their own finite types `S i` of state-action pairs (the
paper's `|S_i| = |S|` is not needed) and `N` is arbitrary. `P` is any transition matrix on
`Joint S`; `μ` is stationary but not assumed unique, and positive only on agent marginals. The
local transition is the published `IsLocalTransitionN` (Appendix H's display multiplied by the
marginal); `μ^π_i` is the agent marginal `marginalDist i μ`. The decomposition `Q` is written with
the Bellman solutions (`IsBellmanQ`). -/
theorem mu_atv_entanglement_bound_multi
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P)
    (μ : Joint S → ℝ) (hμ : IsOccupancyN μ) (hstat : IsStationary P μ)
    (Pπ : ∀ i, Matrix (S i) (S i) ℝ) (hPπ : ∀ i, IsLocalTransitionN i P μ (Pπ i)) :
    (∀ (i : Fin N) (Q : Matrix (Joint S) (Joint S) ℝ) (K : ℕ) (x : Fin K → ℝ)
        (Pj : Fin K → ∀ j, Matrix (S j) (S j) ℝ),
        (∀ k j, IsTransitionMatrix (Pj k j)) → ∑ k, x k = 1 →
        Q = ∑ k, x k • tensorProdN (Pj k) → IsTransitionMatrix Q →
        muATVDistN i μ P Q = muEntanglementN i μ P →
          muInducedNorm (marginalDist i μ) (Pπ i - ∑ k, x k • Pj k i) ≤
            2 * muEntanglementN i μ P) ∧
    ∀ (γ : ℝ), 0 ≤ γ → γ < 1 →
      ∀ (r : ∀ i, S i → ℝ) (rmax : Fin N → ℝ), (∀ i s, |r i s| ≤ rmax i) →
        ∀ (Q : Joint S → ℝ) (Qloc : ∀ i, S i → ℝ),
          IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q →
          (∀ i, IsBellmanQ (Pπ i) (r i) γ (Qloc i)) →
          muNorm μ (fun p => Q p - ∑ i, Qloc i (p i)) ≤
            4 * γ * (∑ i, muEntanglementN i μ P * rmax i) / (1 - γ) ^ 2 := by sorry

end MarkovEntanglementExact.Supplement
