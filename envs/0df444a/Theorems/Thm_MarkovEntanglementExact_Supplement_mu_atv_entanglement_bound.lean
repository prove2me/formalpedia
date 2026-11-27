-- Prove2me | Theorems.Thm_MarkovEntanglementExact_Supplement_mu_atv_entanglement_bound
-- name    : MarkovEntanglementExact.Supplement.mu_atv_entanglement_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:52:38.879882+00:00
-- url     : https://prove2.me/theorems/385e4d36-a1c4-50bd-84f1-c944b44d51c1
-- title:
--   Theorem 5 — the µ-weighted agent-wise measures of entanglement bound the local-transition bias and the µ-norm value-decomposition error
-- statement:
--   Let $P$ be a transition matrix on $X_A\times X_B$ and $\mu$ a stationary distribution of $P$ with positive agent marginals $\mu_A$, $\mu_B$. For a vector $y$ write $\|y\|_\mu=\sum_x\mu(x)|y(x)|$ (Definition 6). The **$\mu$-weighted agent-wise total variation distance** with respect to agent $A$ (Definition 8) is
--   $$\|P-P'\|_{\mu\text{-ATV}_A}=\frac12\sup_{\|x\|_\infty=1}\big\|(P-P')(x\otimes e)\big\|_\mu,$$
--   and $E_A(P)=\min_{P'\in\mathcal P_{\mathrm{SEP}}}\|P-P'\|_{\mu\text{-ATV}_A}$ is the corresponding measure of entanglement (Eq. (4)); $E_B$ is defined with $e\otimes x$. For a matrix $M$ on agent $A$'s pairs let $\|M\|_{\mu_A,\infty}=\sup_{\|x\|_\infty=1}\|Mx\|_{\mu_A}$. Let $P^\pi_A$, $P^\pi_B$ be the local transitions of Eq. (2).
--
--   1. For every optimal solution $\sum_jx_jP^{(j)}_A\otimes P^{(j)}_B$ of $E_A(P)$, with $P_A=\sum_jx_jP^{(j)}_A$,
--   $$\|P^\pi_A-P_A\|_{\mu_A,\infty}\le2E_A(P),$$
--   and likewise $\|P^\pi_B-P_B\|_{\mu_B,\infty}\le2E_B(P)$ for every optimal solution of $E_B(P)$, where $\mu_A$, $\mu_B$ are the agent marginals of $\mu$, which are stationary for $P^\pi_A$, $P^\pi_B$ (Lemma 5).
--   2. For $0\le\gamma<1$ and local rewards with $|r_A|\le r^A_{\max}$, $|r_B|\le r^B_{\max}$,
--   $$\big\|Q_{AB}-(Q_A\otimes e+e\otimes Q_B)\big\|_{\mu}\le\frac{4\gamma\,\big(E_A(P)\,r^A_{\max}+E_B(P)\,r^B_{\max}\big)}{(1-\gamma)^2}.$$
--
--   This is the stationary-distribution-weighted counterpart of Theorem 4: the condition on $P$ is relaxed to an average over the occupancy, and the error is measured in the weaker $\mu$-norm.
--
--   **Formalization Note** The measure is Definition 8's, with the supremum outside the $\mu$-sum (`muATVDistA/B`, `muEntanglementA/B`), not the larger right-hand side of Eq. (7). `‖x‖ = 1` is Mathlib's sup norm.
--
--   Differences from the source:
--   - generalization: P^π_AB, the transition matrix of a two-agent MDP under π, with |S_A| = |S_B| and |A_A| = |A_B| → any transition matrix P on X_A × X_B for arbitrary finite types X_A, X_B of agent state-action pairs; reason: the proof uses only that P is a transition matrix; P^π_AB is an instance (published inducedMatrix_isTransitionMatrix), so the Lean statement specializes to the source
--   - generalization: µ^π_AB the unique stationary distribution of a unichain system → µ any stationary distribution of P with positive agent marginals (IsOccupancy, IsStationary), uniqueness not assumed; reason: the proof uses stationarity but never uniqueness; the paper's µ is an instance
--   - reading: µ^π_i "the stationary distribution of P^π_i" → µ_i the agent marginal of µ (marginalA μ, marginalB μ); reason: Lemma 5 and §5.4 identify the local stationary distribution with the marginal; a stationary distribution of P^π_i need not be unique
--   - encoding: Eq. (2), the local transition as a conditional sum with µ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied by the positive marginal µ_A(s_A, a_A); reason: equivalent when the marginal is positive (footnote 1), which IsOccupancy assumes
--   - encoding: Q-values Q = (I − γP)^{-1} r → Q-values as solutions of the Bellman equation (IsBellmanQ); reason: for 0 ≤ γ < 1 the Bellman equation has exactly the solution (I − γP)^{-1} r
--   - encoding: "where … is an optimal solution of Eq. (4)" → the bound for every optimal solution, quantified universally; reason: the paper does not fix one minimizer; the minimum is attained, so the hypothesis is satisfiable
--   - encoding: P_i, "the optimal solutions of Eq. (4) … w.r.t agent i" → P_A = Σ_j x_j P^(j)_A for an optimal separable transition matrix Σ_j x_j P^(j)_A ⊗ P^(j)_B; reason: the optimal solution only depends on P_A (p.39)
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 5, p.19 (with Definitions 6, 8, pp.18–19, and Lemma 5, p.38)

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_markov_entanglement_multi
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness
import Definitions.Def_MarkovEntanglementExact_IsOccupancy
import Definitions.Def_MarkovEntanglementExact_Supplement_muInducedNorm
import Definitions.Def_MarkovEntanglementExact_Supplement_muATVDistA
import Definitions.Def_MarkovEntanglementExact_Supplement_muATVDistB
import Definitions.Def_MarkovEntanglementExact_Supplement_muEntanglementA
import Definitions.Def_MarkovEntanglementExact_Supplement_muEntanglementB

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- **Theorem 5** (entanglement measured by `μ`-weighted agent-wise total variation). Let `P` be
a transition matrix on the joint state-action pairs of two agents, `μ` a stationary distribution
of `P` with positive agent marginals, `P^π_A`, `P^π_B` the local transitions of Eq. (2), and
`E_A(P)`, `E_B(P)` the measures of Eq. (4) under the `μ`-weighted agent-wise total variation
distance of Definition 8.

1. For every optimal solution `Q = Σ_j x_j P^(j)_A ⊗ P^(j)_B ∈ P_SEP` of Eq. (4) for agent `A`,
   with `P_A = Σ_j x_j P^(j)_A`: `‖P^π_A − P_A‖_{μ_A,∞} ≤ 2E_A(P)`, where `μ_A` is the
   `A`-marginal of `μ` (the stationary distribution of `P^π_A`, Lemma 5); likewise for `B`.
2. For `0 ≤ γ < 1` and local rewards with `|r_A| ≤ r^A_max`, `|r_B| ≤ r^B_max`:
   `‖Q_AB − (Q_A ⊗ e + e ⊗ Q_B)‖_μ ≤ 4γ(E_A(P) r^A_max + E_B(P) r^B_max)/(1 − γ)²`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 5, p.19, with
Definition 8 and the induced norm `‖·‖_{µ,∞}`, p.19, and Lemma 5, p.38.

**Formalization Note.** `P` is any transition matrix on `XA × XB`; `μ` is stationary
(`IsStationary`) but not assumed unique, and positive only on agent marginals. The paper's
`μ^π_i` is taken to be the agent marginal of `μ`, which Lemma 5 shows is stationary for `P^π_i`
(a stationary distribution of `P^π_i` need not be unique). The optimal solution is quantified
universally; `‖y‖_μ = Σ μ |y|` is the published `muNorm`. -/
theorem mu_atv_entanglement_bound
    {XA XB : Type*} [Fintype XA] [Fintype XB] [DecidableEq XA] [DecidableEq XB]
    (P : Matrix (XA × XB) (XA × XB) ℝ) (hP : IsTransitionMatrix P)
    (μ : XA × XB → ℝ) (hμ : IsOccupancy μ) (hstat : IsStationary P μ)
    (PπA : Matrix XA XA ℝ) (PπB : Matrix XB XB ℝ)
    (hPπA : IsLocalTransitionA P μ PπA) (hPπB : IsLocalTransitionB P μ PπB) :
    (∀ (Q : Matrix (XA × XB) (XA × XB) ℝ) (K : ℕ) (x : Fin K → ℝ)
        (PAj : Fin K → Matrix XA XA ℝ) (PBj : Fin K → Matrix XB XB ℝ),
        IsSeparableWitness Q K x PAj PBj → IsTransitionMatrix Q →
        muATVDistA μ P Q = muEntanglementA μ P →
          muInducedNorm (marginalA μ) (PπA - ∑ k, x k • PAj k) ≤ 2 * muEntanglementA μ P) ∧
    (∀ (Q : Matrix (XA × XB) (XA × XB) ℝ) (K : ℕ) (x : Fin K → ℝ)
        (PAj : Fin K → Matrix XA XA ℝ) (PBj : Fin K → Matrix XB XB ℝ),
        IsSeparableWitness Q K x PAj PBj → IsTransitionMatrix Q →
        muATVDistB μ P Q = muEntanglementB μ P →
          muInducedNorm (marginalB μ) (PπB - ∑ k, x k • PBj k) ≤ 2 * muEntanglementB μ P) ∧
    ∀ (γ : ℝ), 0 ≤ γ → γ < 1 →
      ∀ (rA : XA → ℝ) (rB : XB → ℝ) (rAmax rBmax : ℝ),
        (∀ a, |rA a| ≤ rAmax) → (∀ b, |rB b| ≤ rBmax) →
        ∀ (QAB : XA × XB → ℝ) (QA : XA → ℝ) (QB : XB → ℝ),
          IsBellmanQ P (fun p => rA p.1 + rB p.2) γ QAB →
          IsBellmanQ PπA rA γ QA → IsBellmanQ PπB rB γ QB →
          muNorm μ (fun p => QAB p - (QA p.1 + QB p.2)) ≤
            4 * γ * (muEntanglementA μ P * rAmax + muEntanglementB μ P * rBmax) /
              (1 - γ) ^ 2 := by sorry

end MarkovEntanglementExact.Supplement
