-- Prove2me | Theorems.Thm_MarkovEntanglementExact_Supplement_atv_entanglement_bound
-- name    : MarkovEntanglementExact.Supplement.atv_entanglement_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:51:30.908985+00:00
-- url     : https://prove2.me/theorems/9d97277d-6eda-5823-82c4-f32e119e8481
-- title:
--   Theorem 4 — the agent-wise TV measures of entanglement bound the local-transition bias and the entry-wise value-decomposition error
-- statement:
--   Let $P$ be a transition matrix on $X_A\times X_B$, the joint state-action pairs of two agents. The **agent-wise total variation distance** (Definition 5) compares, at every joint pair $x=(x_A,x_B)$, agent $A$'s marginal of the row of $P$ with a candidate local transition $P_A$, and the corresponding measure of entanglement is (Eq. (5))
--   $$E_A(P)=\min_{P_A}\max_{x}\tfrac12\sum_{x_A'}\Big|\sum_{x_B'}P(x,(x_A',x_B'))-P_A(x_A,x_A')\Big|,$$
--   the minimum over transition matrices $P_A$; $E_B(P)$ is defined symmetrically. Let $\mu$ be a probability distribution on $X_A\times X_B$ with positive agent marginals and $P^\pi_A$, $P^\pi_B$ the local transitions of Eq. (2).
--
--   1. For every optimal $P_A$ for agent $A$ and every optimal $P_B$ for agent $B$,
--   $$\|P^\pi_A-P_A\|_{TV}\le E_A(P),\qquad \|P^\pi_B-P_B\|_{TV}\le E_B(P).$$
--   2. For $0\le\gamma<1$ and local rewards with $|r_A|\le r^A_{\max}$, $|r_B|\le r^B_{\max}$, with $Q_{AB}$ the Q-value of $P$ for $r_A\otimes e+e\otimes r_B$ and $Q_A$, $Q_B$ those of $P^\pi_A$, $P^\pi_B$,
--   $$\big\|Q_{AB}-(Q_A\otimes e+e\otimes Q_B)\big\|_\infty\le\frac{4\gamma\,\big(E_A(P)\,r^A_{\max}+E_B(P)\,r^B_{\max}\big)}{(1-\gamma)^2}.$$
--
--   Each agent contributes to the decomposition error through its own entanglement with the system, weighted by its maximal reward; since $E_A,E_B\le E$, this sharpens Theorem 3.
--
--   **Formalization Note** $E_A$, $E_B$ are the published `entanglementA`, `entanglementB`, and the distance the published `agentTVDistA/B`.
--
--   Differences from the source:
--   - generalization: P^π_AB, the transition matrix of a two-agent MDP under π, with |S_A| = |S_B| and |A_A| = |A_B| → any transition matrix P on X_A × X_B for arbitrary finite types X_A, X_B of agent state-action pairs; reason: the proof uses only that P is a transition matrix; P^π_AB is an instance (published inducedMatrix_isTransitionMatrix), so the Lean statement specializes to the source
--   - generalization: µ^π_AB the (unique) stationary distribution of a unichain system (§2, footnote 4) → µ any distribution with positive agent marginals (IsOccupancy), not assumed stationary or unique; reason: the proof uses only Eq. (2) with positive marginals; the paper's stationary occupancy is an instance
--   - encoding: Eq. (2), the local transition as a conditional sum with µ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied by the positive marginal µ_A(s_A, a_A); reason: equivalent when the marginal is positive (footnote 1), which IsOccupancy assumes
--   - encoding: Q-values Q = (I − γP)^{-1} r → Q-values as solutions of the Bellman equation (IsBellmanQ); reason: for 0 ≤ γ < 1 the Bellman equation has exactly the solution (I − γP)^{-1} r
--   - encoding: "where … is an optimal solution of Eq. (4)" → the bound for every optimal solution, quantified universally; reason: the paper does not fix one minimizer; the minimum is attained, so the hypothesis is satisfiable
--   - encoding: ‖v‖_∞ ≤ c for the vector of decomposition errors → |v(p)| ≤ c at every joint pair p; reason: the same statement
--   - encoding: E_A as Eq. (4) under the ATV distance, min over P ∈ P_SEP → E_A as the right-hand side of Eq. (5), min over transition matrices P_A (published entanglementA); reason: the paper states the two minima are equal (Eq. (5)) and that the optimal solution depends only on P_A
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 4, p.16 (with Definition 5, p.15, and Eq. (5), p.16)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsOccupancy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- **Theorem 4** (entanglement measured by agent-wise total variation). Let `P` be a transition
matrix on the joint state-action pairs of two agents, `E_A(P)`, `E_B(P)` its measures of
entanglement with respect to the agent-wise total variation distance (Eq. (5)), `μ` an
occupancy with positive agent marginals and `P^π_A`, `P^π_B` the local transitions of Eq. (2).

1. For every optimal `P_A` of Eq. (5) for agent `A`: `‖P^π_A − P_A‖_TV ≤ E_A(P)`; and for every
   optimal `P_B` for agent `B`: `‖P^π_B − P_B‖_TV ≤ E_B(P)`.
2. For `0 ≤ γ < 1` and local rewards with `|r_A| ≤ r^A_max`, `|r_B| ≤ r^B_max`, at every joint
   pair `|Q_AB − (Q_A ⊗ e + e ⊗ Q_B)| ≤ 4γ(E_A(P) r^A_max + E_B(P) r^B_max)/(1 − γ)²`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 4, p.16, with
Eq. (5), p.16.

**Formalization Note.** `E_A`, `E_B` are the published `entanglementA/B`, the right-hand side of
Eq. (5) (minimum over transition matrices `P_A` of the agent-wise TV distance), which the paper
states equals Eq. (4) under the ATV distance; an optimal solution of Eq. (4) "depends solely on
the closest local transition P_A" (p.16). `P` is any transition matrix on `XA × XB`, `μ` need not
be stationary (positivity on agent marginals only), Q-values are Bellman solutions, and the
vector `‖·‖∞` bound is stated at every joint pair. -/
theorem atv_entanglement_bound
    {XA XB : Type*} [Fintype XA] [Fintype XB] [DecidableEq XA] [DecidableEq XB]
    (P : Matrix (XA × XB) (XA × XB) ℝ) (hP : IsTransitionMatrix P)
    (μ : XA × XB → ℝ) (hμ : IsOccupancy μ)
    (PπA : Matrix XA XA ℝ) (PπB : Matrix XB XB ℝ)
    (hPπA : IsLocalTransitionA P μ PπA) (hPπB : IsLocalTransitionB P μ PπB) :
    (∀ PA : Matrix XA XA ℝ, IsTransitionMatrix PA → agentTVDistA P PA = entanglementA P →
        tvDist PπA PA ≤ entanglementA P) ∧
    (∀ PB : Matrix XB XB ℝ, IsTransitionMatrix PB → agentTVDistB P PB = entanglementB P →
        tvDist PπB PB ≤ entanglementB P) ∧
    ∀ (γ : ℝ), 0 ≤ γ → γ < 1 →
      ∀ (rA : XA → ℝ) (rB : XB → ℝ) (rAmax rBmax : ℝ),
        (∀ a, |rA a| ≤ rAmax) → (∀ b, |rB b| ≤ rBmax) →
        ∀ (QAB : XA × XB → ℝ) (QA : XA → ℝ) (QB : XB → ℝ),
          IsBellmanQ P (fun p => rA p.1 + rB p.2) γ QAB →
          IsBellmanQ PπA rA γ QA → IsBellmanQ PπB rB γ QB →
          ∀ p : XA × XB, |QAB p - (QA p.1 + QB p.2)| ≤
            4 * γ * (entanglementA P * rAmax + entanglementB P * rBmax) / (1 - γ) ^ 2 := by sorry

end MarkovEntanglementExact.Supplement
