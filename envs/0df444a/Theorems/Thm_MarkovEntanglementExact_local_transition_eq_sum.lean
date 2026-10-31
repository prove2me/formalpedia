-- Prove2me | Theorems.Thm_MarkovEntanglementExact_local_transition_eq_sum
-- name    : MarkovEntanglementExact.local_transition_eq_sum
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:43.671174+00:00
-- url     : https://prove2.me/theorems/be4d8012-33f8-42b9-9fc1-458eb25516af
-- title:
--   Theorem 1, first display, p.9 — $P^\pi_A=\sum_jx_jP^{(j)}_A$ and $P^\pi_B=\sum_jx_jP^{(j)}_B$
-- statement:
--   Let $P=\sum_{j=1}^Kx_jP^{(j)}_A\otimes P^{(j)}_B$ be as in Definition 1, $\mu$ a distribution with positive agent marginals, and $P_A,P_B$ the local transition matrices of Eq. (2). Then
--   $$P_A=\sum_{j=1}^Kx_jP^{(j)}_A,\qquad P_B=\sum_{j=1}^Kx_jP^{(j)}_B.$$
--
--   Thus for a separable system the local chain does not depend on the occupancy measure, and it is the chain that local TD learning sees.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - generalization: μ is the stationary occupancy measure of a unichain, unique and strictly positive on states → μ is any distribution on joint pairs with μ ≥ 0, Σμ = 1 and positive agent marginals; reason: the derivation uses only the positivity of the conditioning marginals (footnote 1); the paper's occupancy measure is an instance, proved in the verification file OccupancyInstance
--   - encoding: Eq. (2) with the conditional μ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied through by the marginal; reason: equivalent under positive marginals; the quotient form is proved in M2
--   - reading: first sum printed Σ_{i=1}^K x_j P^(j)_A → the sum over j of x_j P^(j)_A; reason: the index i is a typo for j, as Definition 1 and the second sum show
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_IsSeparableWitness
import Definitions.Def_MarkovEntanglementExact_IsOccupancy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- Theorem 1, first display: if `P = Σ_j x_j P^(j)_A ⊗ P^(j)_B`, then the marginalized local
transition matrices of Eq. (2) are `P_A = Σ_j x_j P^(j)_A` and `P_B = Σ_j x_j P^(j)_B`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9 (the
printed index `i` of the first sum is a typo for `j`). -/
theorem local_transition_eq_sum
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ)
    {K : ℕ} {x : Fin K → ℝ} {PAj : Fin K → Matrix SA SA ℝ} {PBj : Fin K → Matrix SB SB ℝ}
    (hw : IsSeparableWitness P K x PAj PBj)
    (μ : SA × SB → ℝ) (hμ : IsOccupancy μ)
    (PA : Matrix SA SA ℝ) (PB : Matrix SB SB ℝ)
    (hA : IsLocalTransitionA P μ PA) (hB : IsLocalTransitionB P μ PB) :
    PA = ∑ k, x k • PAj k ∧ PB = ∑ k, x k • PBj k := by sorry

end MarkovEntanglementExact
