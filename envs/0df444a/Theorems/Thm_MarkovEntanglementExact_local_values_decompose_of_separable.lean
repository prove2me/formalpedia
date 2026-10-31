-- Prove2me | Theorems.Thm_MarkovEntanglementExact_local_values_decompose_of_separable
-- name    : MarkovEntanglementExact.local_values_decompose_of_separable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:23.715435+00:00
-- url     : https://prove2.me/theorems/8a703e7d-f9e4-4e0d-b787-29b0c73482c6
-- title:
--   Theorem 1, last display, p.9 — $Q^\pi_{AB}=Q^\pi_A\otimes e+e\otimes Q^\pi_B$
-- statement:
--   Let $P$ be a separable transition matrix on $S_A\times S_B$, $0\le\gamma<1$, $\mu$ a distribution with positive agent marginals, and $P_A,P_B$ the local transition matrices of Eq. (2). Then for all local rewards $r_A,r_B$,
--   $$Q=Q_A\otimes e+e\otimes Q_B,$$
--   where $Q$, $Q_A$, $Q_B$ are the Bellman solutions for $(P,r_A\otimes e+e\otimes r_B)$, $(P_A,r_A)$ and $(P_B,r_B)$.
--
--   This is Eq. (1) of the paper for the local Q-values $Q^\pi_A=(I-\gamma P^\pi_A)^{-1}r_A$ and $Q^\pi_B$, which are the limits of local TD learning.
--
--   **Formalization Note** $\gamma=0$ is included, since Theorem 1 does not assume $\gamma>0$.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - generalization: μ is the stationary occupancy measure of a unichain, unique and strictly positive on states → μ is any distribution on joint pairs with μ ≥ 0, Σμ = 1 and positive agent marginals; reason: the derivation uses only the positivity of the conditioning marginals (footnote 1); the paper's occupancy measure is an instance, proved in the verification file OccupancyInstance
--   - encoding: Eq. (2) with the conditional μ(s_B, a_B | s_A, a_A) → IsLocalTransitionA/B, Eq. (2) multiplied through by the marginal; reason: equivalent under positive marginals; the quotient form is proved in M2
--   - encoding: Q-values as the printed expectation, and Q^π_A = (I − γP^π_A)⁻¹ r_A → Q-values as the solutions of IsBellmanQ; reason: M1 proves the solution exists, is unique, and equals the series and the inverse formula
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_LocalValuesDecompose
import Definitions.Def_MarkovEntanglementExact_IsOccupancy

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- Theorem 1, last display: if the agents are separable, then Eq. (1) holds with the local
Q-values of the marginalized chains, `Q^π_AB = Q^π_A ⊗ e + e ⊗ Q^π_B`, for every reward pair and
every `0 ≤ γ < 1`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9.

**Formalization Note.** `γ = 0` is included, since Theorem 1 has no `γ > 0`. -/
theorem local_values_decompose_of_separable
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (hsep : IsSeparable P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : SA × SB → ℝ) (hμ : IsOccupancy μ)
    (PA : Matrix SA SA ℝ) (PB : Matrix SB SB ℝ)
    (hA : IsLocalTransitionA P μ PA) (hB : IsLocalTransitionB P μ PB) :
    LocalValuesDecompose P PA PB γ := by sorry

end MarkovEntanglementExact
