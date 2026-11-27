-- Prove2me | Theorems.Thm_MarkovEntanglementExact_Supplement_exogenous_entanglement_bound
-- name    : MarkovEntanglementExact.Supplement.exogenous_entanglement_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:54:23.095249+00:00
-- url     : https://prove2.me/theorems/4af8fc10-03a0-445c-808d-b3698bbb8060
-- title:
--   Theorem 9 — with exogenous information, the agent-wise measures of entanglement bound the local-transition bias and the entry-wise value-decomposition error
-- statement:
--   Consider $N$ agents with finite sets $S_i$ of state-action pairs and a finite set $\mathcal Z$ of exogenous states. Let $P$ be a transition matrix on triples $(s,a,z)$ (the joint pair of all agents and $z$), $\mu$ a probability distribution on them whose marginals $\mu_{iz}(s_i,a_i,z)$ are positive for every agent, and $P^\pi_{iz}$ agent $i$'s local transition
--   $$P^\pi_{iz}(s_i',a_i',z'\mid s_i,a_i,z)=\sum_{s_{-i},a_{-i}}\mu(s_{-i},a_{-i}\mid s_i,a_i,z)\sum_{s'_{-i},a'_{-i}}P(s',a',z'\mid s,a,z).$$
--   The measure of entanglement of agent $i$ with exogenous information (Eq. (13)) is
--   $$E_i(P,\mathcal Z)=\min_{P_{iz}}\max_{s,a,z}\tfrac12\sum_{s_i',a_i',z'}\big|P(s_i',a_i',z'\mid s,a,z)-P_{iz}(s_i',a_i',z'\mid s_i,a_i,z)\big|,$$
--   the minimum over transition matrices $P_{iz}$ on agent $i$'s pairs and $\mathcal Z$.
--
--   1. For every agent $i$ and every optimal $P_{iz}$ (the paper's $\sum_jx_jP^{(j)}_{iz}$),
--   $$\|P^\pi_{iz}-P_{iz}\|_\infty\le2E_i(P,\mathcal Z),$$
--   with $\|\cdot\|_\infty$ the induced $\ell_\infty$ matrix norm.
--   2. For $0\le\gamma<1$ and local rewards $r_i(s_i,a_i,z)$ with $|r_i|\le r^i_{\max}$, with $Q$ the Q-value of $P$ for $\sum_ir_i(s_i,a_i,z)$ and $Q_{iz}$ that of $P^\pi_{iz}$ for $r_i$,
--   $$\Big\|Q(s,a,z)-\sum_{i=1}^NQ_{iz}(s_i,a_i,z)\Big\|_\infty\le\frac{4\gamma\sum_{i=1}^NE_i(P,\mathcal Z)\,r^i_{\max}}{(1-\gamma)^2}.$$
--
--   Shared exogenous signals (orders in ride-hailing, tasks in warehouse routing) couple the agents; the theorem shows that value decomposition conditioned on the signal remains controlled by agent-wise entanglement.
--
--   **Formalization Note** Triples are the published `JointZ S Z` and the row marginal the published `marginalZ`.
--
--   Differences from the source:
--   - generalization: P^π_ABz(s′, a′, z′ | s, a, z) = P(s′ | s, a, z) π(a′ | s′, z′) P(z′ | z) with z an independent Markov chain → any transition matrix P on JointZ S Z; reason: the proof uses only that P is a transition matrix; the structured matrix is an instance
--   - generalization: µ^π_ABz the unique stationary distribution of a unichain system → µ any distribution with positive (s_i, a_i, z) marginals (IsOccupancyZ); reason: the proof uses only the local transition's defining identity; the paper's µ is an instance
--   - generalization: one reward function r(s_{i,t}, a_{i,t}, z_t) for every agent (p.45), bounded per agent by r^i_max (Theorem 9) → an agent-specific reward r_i : S_i × Z → ℝ with |r_i| ≤ r^i_max; reason: a common reward is the case r_i = r; the proof treats each agent's reward separately
--   - reading: Q^π(s, a, z) = E[Σ_t Σ_i r(s_{i,t}, a_{i,t}, z_t)] (printed without γ^t) → Q-values as Bellman solutions with discount γ (IsBellmanQ); reason: p.45 defines the local values by the Bellman equation Q^π_Az = (I − γP_Az)^{-1} r_Az and the bound has γ
--   - reading: "any policy π: S → ∆(A)" → no policy; P any transition matrix (covering π: S × Z → ∆(Ã) of the model); reason: the model of Appendix J.1 lets π depend on z
--   - reading: ‖P^π_iz − Σ_j x_j P^(j)_iz‖_∞ with Σ_j x_j P^(j)_iz an optimal solution of Eq. (13) → ‖P^π_iz − P_iz‖ for every transition matrix P_iz attaining the minimum in Eq. (13)'s second form; reason: Eq. (13) equates the two forms; the optimal Σ_j x_j P^(j)_iz is a minimizer of the second
--   - reading: Eq. (13)'s first form min ½‖P^π_ABz − Σ_j x_j P^(j)_Az ⊗ P^(j)_B‖_ATV1 carries a factor ½ in front of an agent-wise TV distance that already contains D_TV's ½, so it is half of the second form min_{P_Az} max_{s,a,z} ½ Σ |P^π_ABz(s′_A, a′_A, z′ | s, a, z) − P_Az(s′_A, a′_A, z′ | s_A, a_A, z)| that the paper equates it with → E_i(P, Z) is the second, explicit form (exoEntanglement, without the extra ½); reason: the second form is the analogue of Eq. (5) ("Similar to Theorem 4"); with the halved first form clause 1 is false (N = 2, trivial Z: agent 1 at s_1 sees next-state marginals δ_0 or δ_1 according to agent 2's pair, μ puts all of s_1's mass on the δ_0 row; the unique minimizer row is (½, ½), E = ½, and the row sum |δ_0 − (½, ½)| = 1 = 2E exceeds 2 · ½E)
--   - reading: P_Az uses the conditional µ^π_ABz(s_B, a_B | s_A, a_A, z) (p.45), defined only where the marginal µ(s_A, a_A, z) is positive (footnote 1, p.8: pairs of zero occupancy are excluded) → IsOccupancyZ requires the marginal µ_iz(s_i, a_i, z) to be positive for every agent i and every triple; reason: the local transition, and with it the theorem, is undefined at a triple of zero marginal; this is footnote 1's convention carried to (s_i, a_i, z)
--   - encoding: the local transition with the conditional µ(s_{−i}, a_{−i} | s_i, a_i, z) → IsLocalTransitionZ, multiplied by the positive marginal; reason: equivalent when the marginal is positive
--   - encoding: ‖M‖_∞ (induced ℓ∞ norm) → Σ_t |M(s, t)| ≤ c for every row s; reason: the induced ℓ∞ norm is the maximum absolute row sum
--   - encoding: ‖v‖_∞ ≤ c for the vector of decomposition errors → |v(p)| ≤ c at every joint pair p; reason: the same statement
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 9, p.46 (with Eq. (13), p.46, and Appendix J.1, pp.44–45)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_Supplement_IsOccupancyZ
import Definitions.Def_MarkovEntanglementExact_Supplement_IsLocalTransitionZ
import Definitions.Def_MarkovEntanglementExact_Supplement_exoATVDist
import Definitions.Def_MarkovEntanglementExact_Supplement_exoEntanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- **Theorem 9** (exogenous information). Let `P` be a transition matrix on the triples
`(s, a, z)` of the joint state-action pair of `N` agents and an exogenous state `z ∈ 𝒵`, `μ` an
occupancy whose marginals on every `(s_i, a_i, z)` are positive, `P^π_{iz}` agent `i`'s local
transition with exogenous information (Appendix J.1), and `E_i(P, 𝒵)` the measure of Eq. (13).

1. For every agent `i` and every optimal `P_{iz}` of Eq. (13) (the paper's
   `Σ_j x_j P^(j)_{iz}`): `‖P^π_{iz} − P_{iz}‖_∞ ≤ 2E_i(P, 𝒵)`, with `‖·‖_∞` the induced matrix
   norm (maximum absolute row sum).
2. For `0 ≤ γ < 1` and local rewards `r_i(s_i, a_i, z)` with `|r_i| ≤ r^i_max`, the global
   Q-value `Q` of `P` for `Σ_i r_i(s_i, a_i, z)` and the local Q-values `Q_{iz}` of `P^π_{iz}`
   satisfy, at every `(s, a, z)`,
   `|Q(s, a, z) − Σ_i Q_{iz}(s_i, a_i, z)| ≤ 4γ(Σ_i E_i(P, 𝒵) r^i_max)/(1 − γ)²`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 9, p.46, with
Eq. (13), p.46, and the model, local transition and Bellman equation of Appendix J.1, pp.44–45.

**Formalization Note.** `P` is any transition matrix on `JointZ S Z`; the paper's
`P(s′ | s, a, z) π(a′ | s′, z′) P(z′ | z)` is an instance. The Q-values are the Bellman solutions
(p.45: `Q^π_Az = (I − γP_Az)^{-1} r_Az`), the printed expectation having dropped `γ^t`; `π` may
depend on `z` (the model's `π : S × Z → Δ(Ã)`). `μ` need not be stationary or unique. The
optimal solution is quantified universally; matrix and vector `‖·‖_∞` bounds are stated row by
row and point by point. -/
theorem exogenous_entanglement_bound
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (hP : IsTransitionMatrix P)
    (μ : JointZ S Z → ℝ) (hμ : IsOccupancyZ μ)
    (Pπ : ∀ i, Matrix (S i × Z) (S i × Z) ℝ) (hPπ : ∀ i, IsLocalTransitionZ i P μ (Pπ i)) :
    (∀ (i : Fin N) (Piz : Matrix (S i × Z) (S i × Z) ℝ), IsTransitionMatrix Piz →
        exoATVDist i P Piz = exoEntanglement i P →
        ∀ s : S i × Z, ∑ t, |Pπ i s t - Piz s t| ≤ 2 * exoEntanglement i P) ∧
    ∀ (γ : ℝ), 0 ≤ γ → γ < 1 →
      ∀ (r : ∀ i, S i × Z → ℝ) (rmax : Fin N → ℝ), (∀ i t, |r i t| ≤ rmax i) →
        ∀ (Q : JointZ S Z → ℝ) (Qloc : ∀ i, S i × Z → ℝ),
          IsBellmanQ P (fun p => ∑ i, r i (p.1 i, p.2)) γ Q →
          (∀ i, IsBellmanQ (Pπ i) (r i) γ (Qloc i)) →
          ∀ p : JointZ S Z, |Q p - ∑ i, Qloc i (p.1 i, p.2)| ≤
            4 * γ * (∑ i, exoEntanglement i P * rmax i) / (1 - γ) ^ 2 := by sorry

end MarkovEntanglementExact.Supplement
