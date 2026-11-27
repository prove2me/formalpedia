-- Prove2me | Theorems.Thm_MarkovEntanglementExact_Supplement_tv_entanglement_bound
-- name    : MarkovEntanglementExact.Supplement.tv_entanglement_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:51:07.206319+00:00
-- url     : https://prove2.me/theorems/c831bf33-7041-5a7d-ad61-e33ca944af46
-- title:
--   Theorem 3 — the TV measure of Markov entanglement bounds the local-transition bias and the entry-wise value-decomposition error
-- statement:
--   Let $X_A$, $X_B$ be the finite sets of state-action pairs of two agents and $P$ a transition matrix on $X_A\times X_B$ (for instance $P^\pi_{AB}$ of a two-agent MDP under a policy $\pi$). Let $\mathcal P_{\mathrm{SEP}}$ be the set of separable transition matrices $\sum_{j=1}^K x_jP^{(j)}_A\otimes P^{(j)}_B$ (Definition 1, with $\sum_jx_j=1$, transition matrices $P^{(j)}_A$, $P^{(j)}_B$, and the sum itself a transition matrix), and let
--   $$E(P)=\min_{P'\in\mathcal P_{\mathrm{SEP}}}\|P-P'\|_{TV},\qquad \|P-P'\|_{TV}=\max_{x}\tfrac12\sum_{y}|P(x,y)-P'(x,y)|,$$
--   be the measure of Markov entanglement with respect to the total variation distance. Let $\mu$ be a probability distribution on $X_A\times X_B$ with positive agent marginals $\mu_A$, $\mu_B$, and $P^\pi_A$, $P^\pi_B$ the local transitions of Eq. (2): $P^\pi_A(x_A,x_A')=\sum_{x_B}\mu(x_B\mid x_A)\sum_{x_B'}P((x_A,x_B),(x_A',x_B'))$, and symmetrically for $B$.
--
--   1. For every optimal solution $\sum_jx_jP^{(j)}_A\otimes P^{(j)}_B$ of the minimum,
--   $$\Big\|P^\pi_A-\sum_{j=1}^Kx_jP^{(j)}_A\Big\|_{TV}\le E(P),\qquad \Big\|P^\pi_B-\sum_{j=1}^Kx_jP^{(j)}_B\Big\|_{TV}\le E(P).$$
--   2. For a discount factor $0\le\gamma<1$ and local rewards $r_A$, $r_B$ with $|r_A|\le r^A_{\max}$, $|r_B|\le r^B_{\max}$, let $Q_{AB}$ be the Q-value of $P$ for the reward $r_A\otimes e+e\otimes r_B$, and $Q_A$, $Q_B$ the Q-values of $P^\pi_A$, $P^\pi_B$ for $r_A$, $r_B$ (solutions of the Bellman equation $Q=r+\gamma PQ$). Then
--   $$\big\|Q_{AB}-(Q_A\otimes e+e\otimes Q_B)\big\|_\infty\le\frac{4\gamma E(P)\,(r^A_{\max}+r^B_{\max})}{(1-\gamma)^2}.$$
--
--   The theorem extends Theorem 1 quantitatively: when $E(P)=0$ the system is separable and the decomposition is exact, and in general the bias of the locally learned transitions and the entry-wise decomposition error are controlled by the distance to the nearest separable system.
--
--   **Formalization Note** $E(P)$ is `tvEntanglement P`, an `sInf` over separable transition matrices; an optimal solution is given by a witness `IsSeparableWitness Q K x PAj PBj` with `IsTransitionMatrix Q` and `tvDist P Q = tvEntanglement P`.
--
--   Differences from the source:
--   - generalization: P^π_AB, the transition matrix of a two-agent MDP under π, with |S_A| = |S_B| and |A_A| = |A_B| → any transition matrix P on X_A × X_B for arbitrary finite types X_A, X_B of agent state-action pairs; reason: the proof uses only that P is a transition matrix; P^π_AB is an instance (published inducedMatrix_isTransitionMatrix), so the Lean statement specializes to the source
--   - generalization: µ^π_AB the (unique) stationary distribution of a unichain system (§2, footnote 4) → µ any distribution with positive agent marginals (IsOccupancy), not assumed stationary or unique; reason: the proof uses only Eq. (2) with positive marginals; the paper's stationary occupancy is an instance
--   - encoding: Eq. (2), the local transition as a conditional sum with µ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied by the positive marginal µ_A(s_A, a_A); reason: equivalent when the marginal is positive (footnote 1), which IsOccupancy assumes
--   - encoding: Q-values Q = (I − γP)^{-1} r → Q-values as solutions of the Bellman equation (IsBellmanQ); reason: for 0 ≤ γ < 1 the Bellman equation has exactly the solution (I − γP)^{-1} r
--   - encoding: "where … is an optimal solution of Eq. (4)" → the bound for every optimal solution, quantified universally; reason: the paper does not fix one minimizer; the minimum is attained, so the hypothesis is satisfiable
--   - encoding: ‖v‖_∞ ≤ c for the vector of decomposition errors → |v(p)| ≤ c at every joint pair p; reason: the same statement
--   - encoding: P_SEP, "the set of all separable transition matrices" (Eq. (4); p.12 requires its elements to be transition matrices) → IsSeparable Q ∧ IsTransitionMatrix Q, with min written sInf; reason: the minimum is attained (compact feasible set), so sInf is the minimum
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 3, p.15 (with Definitions 3, 4, Eq. (4), pp.14–15)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness
import Definitions.Def_MarkovEntanglementExact_IsOccupancy
import Definitions.Def_MarkovEntanglementExact_Supplement_tvEntanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- **Theorem 3** (entanglement measured by total variation). Let `P` be a transition matrix on
the joint state-action pairs of two agents, `E(P) = min_{P′ ∈ P_SEP} ‖P − P′‖_TV`, `μ` an
occupancy with positive agent marginals and `P^π_A`, `P^π_B` the local transitions of Eq. (2).

1. For every optimal solution `Q = Σ_j x_j P^(j)_A ⊗ P^(j)_B ∈ P_SEP` of Eq. (4):
   `‖P^π_A − Σ_j x_j P^(j)_A‖_TV ≤ E(P)` and `‖P^π_B − Σ_j x_j P^(j)_B‖_TV ≤ E(P)`.
2. For `0 ≤ γ < 1` and local rewards with `|r_A| ≤ r^A_max`, `|r_B| ≤ r^B_max`, the global
   Q-value `Q_AB` of `P` for `r_A ⊗ e + e ⊗ r_B` and the local Q-values `Q_A`, `Q_B` of
   `P^π_A`, `P^π_B` satisfy, at every joint pair,
   `|Q_AB − (Q_A ⊗ e + e ⊗ Q_B)| ≤ 4γ E(P)(r^A_max + r^B_max)/(1 − γ)²`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 3, p.15.

**Formalization Note.** `P` is any transition matrix on `XA × XB` (finite types of agent
state-action pairs, possibly of different sizes); the MDP-induced `P^π_AB` is an instance
(published `inducedMatrix_isTransitionMatrix`). `μ` need not be stationary or unique; positivity
is on agent marginals only (`IsOccupancy`). Local transitions are given by the multiplicative
form of Eq. (2) (`IsLocalTransitionA/B`), Q-values as solutions of the Bellman equation
(`IsBellmanQ`). The optimal solution is quantified universally; the vector `‖·‖∞` bound is stated
at every joint pair. -/
theorem tv_entanglement_bound
    {XA XB : Type*} [Fintype XA] [Fintype XB] [DecidableEq XA] [DecidableEq XB]
    (P : Matrix (XA × XB) (XA × XB) ℝ) (hP : IsTransitionMatrix P)
    (μ : XA × XB → ℝ) (hμ : IsOccupancy μ)
    (PπA : Matrix XA XA ℝ) (PπB : Matrix XB XB ℝ)
    (hPπA : IsLocalTransitionA P μ PπA) (hPπB : IsLocalTransitionB P μ PπB) :
    (∀ (Q : Matrix (XA × XB) (XA × XB) ℝ) (K : ℕ) (x : Fin K → ℝ)
        (PAj : Fin K → Matrix XA XA ℝ) (PBj : Fin K → Matrix XB XB ℝ),
        IsSeparableWitness Q K x PAj PBj → IsTransitionMatrix Q →
        tvDist P Q = tvEntanglement P →
          tvDist PπA (∑ k, x k • PAj k) ≤ tvEntanglement P ∧
          tvDist PπB (∑ k, x k • PBj k) ≤ tvEntanglement P) ∧
    ∀ (γ : ℝ), 0 ≤ γ → γ < 1 →
      ∀ (rA : XA → ℝ) (rB : XB → ℝ) (rAmax rBmax : ℝ),
        (∀ a, |rA a| ≤ rAmax) → (∀ b, |rB b| ≤ rBmax) →
        ∀ (QAB : XA × XB → ℝ) (QA : XA → ℝ) (QB : XB → ℝ),
          IsBellmanQ P (fun p => rA p.1 + rB p.2) γ QAB →
          IsBellmanQ PπA rA γ QA → IsBellmanQ PπB rB γ QB →
          ∀ p : XA × XB, |QAB p - (QA p.1 + QB p.2)| ≤
            4 * γ * tvEntanglement P * (rAmax + rBmax) / (1 - γ) ^ 2 := by sorry

end MarkovEntanglementExact.Supplement
