-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_observation_1_ii
-- name    : NoLocalBroadcast.Broadcast.observation_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:34:59.222985+00:00
-- url     : https://prove2.me/theorems/3d907f1c-56a8-4efe-b2bf-4a25c19a6662
-- title:
--   Observation 1(ii) (p. 2) — I ≥ I_CQ ≥ I_CC ≥ 0
-- statement:
--   For every state $\rho$ of a finite-dimensional bipartite system $A\otimes B$,
--
--   $$I(\rho)\ \ge\ I_{CQ}(\rho)\ \ge\ I_{CC}(\rho)\ \ge\ 0 .$$
--
--   The chain orders the total correlations, the correlations surviving a measurement on $A$, and those surviving measurements on both sides. In particular it shows that the suprema defining $I_{CQ}$ and $I_{CC}$ are finite.
--
--   **Formalization Note** $I_{CQ}$ and $I_{CC}$ are suprema over POVMs with any finite number of outcomes.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: I_CQ, I_CC as maxima over measurement maps with an orthonormal register → sSup over POVMs with any finite number n of outcomes, the outcome written in the computational basis of Fin n; reason: the maximum is attained in finite dimension, so sSup is the paper's value; any other orthonormal register gives a unitarily equivalent state with the same entropies
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 2, Observation 1(ii)

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Observation 1(ii), p. 2: `I ≥ I_CQ ≥ I_CC ≥ 0` for every state. -/
theorem observation_1_ii {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    I_CQ ρ ≤ mutualInfo ρ ∧ I_CC ρ ≤ I_CQ ρ ∧ 0 ≤ I_CC ρ := by sorry

end NoLocalBroadcast.Broadcast
