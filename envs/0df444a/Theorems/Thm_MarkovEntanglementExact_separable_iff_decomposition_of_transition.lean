-- Prove2me | Theorems.Thm_MarkovEntanglementExact_separable_iff_decomposition_of_transition
-- name    : MarkovEntanglementExact.separable_iff_decomposition_of_transition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:30.708931+00:00
-- url     : https://prove2.me/theorems/628a8272-d83a-4c1b-982d-9f23f24ed571
-- title:
--   p.12 — the sufficient and necessary condition for a transition matrix
-- statement:
--   Let $P$ be a transition matrix on a product $S_A\times S_B$ of finite sets and $0\le\gamma<1$. Then:
--
--   1. if $P$ is separable, $P$ has an exact value decomposition by reward-local maps;
--   2. if $\gamma>0$ and $P$ has such a decomposition, $P$ is separable;
--   3. for every distribution $\mu$ with positive agent marginals and the local transition matrices $P_A,P_B$ of Eq. (2):
--      - $P_A$ and $P_B$ are transition matrices;
--      - for every decomposition $P=\sum_jx_jP^{(j)}_A\otimes P^{(j)}_B$, one has $P_A=\sum_jx_jP^{(j)}_A$ and $P_B=\sum_jx_jP^{(j)}_B$;
--      - if $P$ is separable, the local Q-values of $P_A,P_B$ decompose the Q-value of $P$ for every reward pair;
--      - if $\gamma>0$ and they do so for every reward pair, $P$ is separable.
--
--   This is the mission's goal for a bare transition matrix, with no MDP structure.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - generalization: μ is the stationary occupancy measure of a unichain, unique and strictly positive on states → μ is any distribution on joint pairs with μ ≥ 0, Σμ = 1 and positive agent marginals; reason: the derivation uses only the positivity of the conditioning marginals (footnote 1); the paper's occupancy measure is an instance, proved in the verification file OccupancyInstance
--   - encoding: Eq. (2) with the conditional μ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied through by the marginal; reason: equivalent under positive marginals; the quotient form is proved in M2
--   - encoding: Q-values as the printed expectation, and Q^π_A = (I − γP^π_A)⁻¹ r_A → Q-values as the solutions of IsBellmanQ; reason: M1 proves the solution exists, is unique, and equals the series and the inverse formula
--   - reading: first sum printed Σ_{i=1}^K x_j P^(j)_A → the sum over j of x_j P^(j)_A; reason: the index i is a typo for j, as Definition 1 and the second sum show
--   - generalization: Theorem 1 states its conclusion for the local values of the marginalized chains under μ → clause 1 additionally gives reward-local maps for every separable P, with no occupancy measure (the μ form is kept in clause 3); reason: the maps are the Bellman solutions of the transition matrices Σ_j x_j P^(j)_A and Σ_j x_j P^(j)_B (M3), and this is the hypothesis form of Theorem 2 that the equivalence joins to
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9, Theorem 2, p.12, and the following sentence, p.12

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness
import Definitions.Def_MarkovEntanglementExact_HasExactValueDecomposition
import Definitions.Def_MarkovEntanglementExact_LocalValuesDecompose
import Definitions.Def_MarkovEntanglementExact_IsOccupancy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- "A sufficient and necessary condition" for a transition matrix: for a transition matrix `P`
on a product of two finite sets and `0 ≤ γ < 1`, separability implies the exact value
decomposition, the converse holds when `γ > 0`, and for every occupancy `μ` the marginalized
chains of Eq. (2) are transition matrices, equal `Σ_j x_j P^(j)_A` and `Σ_j x_j P^(j)_B` for every
decomposition of `P`, and their local Q-values decompose the global one for every reward pair
exactly when `P` is separable (the "if" part needing `γ > 0`).

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9,
Theorem 2, p.12, and the sentence following Theorem 2, p.12. -/
theorem separable_iff_decomposition_of_transition
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (IsSeparable P → HasExactValueDecomposition P γ) ∧
      (0 < γ → HasExactValueDecomposition P γ → IsSeparable P) ∧
      ∀ μ : SA × SB → ℝ, IsOccupancy μ →
        ∀ (PA : Matrix SA SA ℝ) (PB : Matrix SB SB ℝ),
          IsLocalTransitionA P μ PA → IsLocalTransitionB P μ PB →
            IsTransitionMatrix PA ∧ IsTransitionMatrix PB ∧
            (∀ (K : ℕ) (x : Fin K → ℝ) (PAj : Fin K → Matrix SA SA ℝ)
                (PBj : Fin K → Matrix SB SB ℝ),
              IsSeparableWitness P K x PAj PBj →
                PA = ∑ k, x k • PAj k ∧ PB = ∑ k, x k • PBj k) ∧
            (IsSeparable P → LocalValuesDecompose P PA PB γ) ∧
            (0 < γ → LocalValuesDecompose P PA PB γ → IsSeparable P) := by sorry

end MarkovEntanglementExact
