-- Prove2me | Theorems.Thm_MarkovEntanglementExact_separable_implies_decomposition
-- name    : MarkovEntanglementExact.separable_implies_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:37.208982+00:00
-- url     : https://prove2.me/theorems/bc519441-6fc3-4c06-97d6-c00fce5b037a
-- title:
--   Theorem 1, p.9, in the form of Theorem 2's hypothesis — separability gives reward-local maps
-- statement:
--   Let $P$ be a separable transition matrix on $S_A\times S_B$ and $0\le\gamma<1$. Then there are maps $\hat Q_A,\hat Q_B$, each reading only its own agent's reward, such that for all $r_A,r_B$ the Q-value of $P$ for the reward $r_A\otimes e+e\otimes r_B$ is
--   $$Q=\hat Q_A(r_A)\otimes e+e\otimes\hat Q_B(r_B).$$
--
--   This is sufficiency in exactly the form of the hypothesis of Theorem 2, so that the two can be joined into an equivalence. No occupancy measure is involved.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - generalization: Theorem 1 takes the local values of the marginalized chains under μ → local maps with no occupancy measure; reason: the maps exist for every separable P, using the transition matrix Σ_j x_j P^(j)_A of M3
--   - encoding: Q-values as the printed expectation, and Q^π_A = (I − γP^π_A)⁻¹ r_A → Q-values as the solutions of IsBellmanQ; reason: M1 proves the solution exists, is unique, and equals the series and the inverse formula
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9, with the hypothesis of Theorem 2, p.12

import Mathlib
import Definitions.Def_markov_entanglement
import Definitions.Def_MarkovEntanglementExact_HasExactValueDecomposition

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- Sufficiency in the local-map form of Theorem 2's hypothesis: if a transition matrix is
separable, the exact decomposition holds with maps reading only their own agent's reward, for
every `0 ≤ γ < 1`. No occupancy measure is involved.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Theorem 1, p.9, in the
hypothesis shape of Theorem 2, p.12. The `N`-agent form is published as
`MarkovEntanglement.separable_implies_value_decomposition_local_maps`. -/
theorem separable_implies_decomposition
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (hP : IsTransitionMatrix P)
    (hsep : IsSeparable P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    HasExactValueDecomposition P γ := by sorry

end MarkovEntanglementExact
