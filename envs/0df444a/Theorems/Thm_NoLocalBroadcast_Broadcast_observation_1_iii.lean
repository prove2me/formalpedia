-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_observation_1_iii
-- name    : NoLocalBroadcast.Broadcast.observation_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:26.909984+00:00
-- url     : https://prove2.me/theorems/b913eedf-1f3a-43c7-9fef-63a81aa8f73c
-- title:
--   Observation 1(iii) (p. 2) — I, I_CQ and I_CC vanish if and only if the state is factorized
-- statement:
--   Let $\rho$ be a state of a finite-dimensional bipartite system $A\otimes B$, with reductions $\rho_A=\operatorname{Tr}_B\rho$ and $\rho_B=\operatorname{Tr}_A\rho$. Then each of the following holds:
--
--   1. $I(\rho)=0$ if and only if $\rho=\rho_A\otimes\rho_B$;
--   2. $I_{CQ}(\rho)=0$ if and only if $\rho=\rho_A\otimes\rho_B$;
--   3. $I_{CC}(\rho)=0$ if and only if $\rho=\rho_A\otimes\rho_B$.
--
--   In the proof of Theorem 3 this turns the vanishing of $I_{CC}$ on the conditional states $\rho^{ij}_{A'B'}$ into their factorization.
--
--   **Formalization Note** "Factorized" is written with the state's own reductions, $\rho=\rho_A\otimes\rho_B$; a state of the form $\alpha\otimes\beta$ with states $\alpha$, $\beta$ has $\alpha=\rho_A$ and $\beta=\rho_B$.
--
--   Differences from the source:
--   - encoding: the state is factorized → ρ = traceRight ρ ⊗ₖ traceLeft ρ; reason: a product of two states α ⊗ β has reductions α and β, so the two conditions coincide
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: I_CQ, I_CC as maxima over measurement maps with an orthonormal register → sSup over POVMs with any finite number n of outcomes, the outcome written in the computational basis of Fin n; reason: the maximum is attained in finite dimension, so sSup is the paper's value; any other orthonormal register gives a unitarily equivalent state with the same entropies
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 2, Observation 1(iii)

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Observation 1(iii), p. 2: each of `I`, `I_CQ`, `I_CC` vanishes if and only if the state is
factorized, `ρ = ρ_A ⊗ ρ_B` with its own reductions. -/
theorem observation_1_iii {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    (mutualInfo ρ = 0 ↔ ρ = QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ) ∧
      (I_CQ ρ = 0 ↔ ρ = QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ) ∧
      (I_CC ρ = 0 ↔ ρ = QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ) := by sorry

end NoLocalBroadcast.Broadcast
