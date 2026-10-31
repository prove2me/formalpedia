-- Prove2me | Theorems.Thm_MarkovEntanglementExact_bellman_unique_solution
-- name    : MarkovEntanglementExact.bellman_unique_solution
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:33.233983+00:00
-- url     : https://prove2.me/theorems/6120c32c-deda-4bb9-9afb-053ee59f10d3
-- title:
--   §2, p.7 — the Bellman equation has the unique solution $(I-\gamma P)^{-1}r$, the discounted series
-- statement:
--   Let $P$ be a transition matrix on a finite set, $0\le\gamma<1$, and $r$ a reward vector. Then $I-\gamma P$ is invertible, and $Q=(I-\gamma P)^{-1}r$ is the unique solution of the Bellman equation
--   $$Q=r+\gamma PQ.$$
--   Moreover
--   $$(I-\gamma P)^{-1}r=\sum_{t=0}^\infty\gamma^tP^tr.$$
--
--   This ties the Bellman solutions used throughout the mission to the printed definition of the Q-value as an expected discounted sum, and shows that a statement quantified over solutions of the Bellman equation is about exactly one vector.
--
--   **Formalization Note** $P^tr$ at an index is the expected reward at time $t$ started from that index. The series converges in the product topology on vectors.
--
--   Differences from the source:
--   - generalization: P^π_AB of a two-agent MDP and policy → an arbitrary transition matrix P on a product of two finite sets; reason: the argument uses only the stochasticity of P; P^π_AB is an instance by M12
--   - encoding: Q^π_AB as the expectation of the discounted reward → the sum of the series Σ_t γ^t P^t r; reason: P^t r at an index is the expected reward at time t from that index
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7

import Mathlib
import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact

/-- The Bellman equation at discount `0 ≤ γ < 1` for a transition matrix `P`: `I − γP` is
invertible, `Q = (I − γP)⁻¹ r` solves `Q = r + γPQ`, it is the only solution, and it is the sum
of the series `Σ_t γ^t P^t r`, which is the printed definition of the Q-value.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, §2, p.7.

**Formalization Note.** `P ^ t *ᵥ r` at an index is the expected reward at time `t` from that
index, so `Σ_t γ^t P^t r` is the expectation in the printed `Q^π_AB`. At `γ = 0` the series is
`r` alone, with `0 ^ 0 = 1`. -/
theorem bellman_unique_solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (r : ι → ℝ) :
    IsUnit (1 - γ • P) ∧
      IsBellmanQ P r γ ((1 - γ • P)⁻¹.mulVec r) ∧
      (∀ Q : ι → ℝ, IsBellmanQ P r γ Q → Q = (1 - γ • P)⁻¹.mulVec r) ∧
      HasSum (fun t : ℕ => γ ^ t • (P ^ t).mulVec r) ((1 - γ • P)⁻¹.mulVec r) := by sorry

end MarkovEntanglementExact
