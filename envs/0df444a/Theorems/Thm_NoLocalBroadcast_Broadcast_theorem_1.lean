-- Prove2me | Theorems.Thm_NoLocalBroadcast_Broadcast_theorem_1
-- name    : NoLocalBroadcast.Broadcast.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:17.646458+00:00
-- url     : https://prove2.me/theorems/e58434d3-7d3d-4458-a6a6-e58bbf5d2553
-- title:
--   Theorem 1 (p. 2) — I_CC(ρ) = I(ρ) if and only if ρ is classical-classical
-- statement:
--   For every state $\rho$ of a finite-dimensional bipartite system $A\otimes B$,
--
--   $$I_{CC}(\rho)=I(\rho)\iff\rho\text{ is classical-classical.}$$
--
--   That is, the correlations of $\rho$ that local measurements can transfer to classical registers amount to all of its correlations exactly when $\rho$ is the embedding of a joint probability distribution in a pair of orthonormal families. This is the paper's first main result; the proof of Theorem 3 ends with it.
--
--   **Formalization Note** $I_{CC}$ is the supremum over pairs of finite POVMs.
--
--   Differences from the source:
--   - encoding: finite-dimensional systems A, B and quantum states → nonempty finite index types a, b; states are positive semidefinite trace-one matrices (QAlgorithms.IsDensityMatrix), A the first factor of a × b; reason: the paper works in finite dimension throughout; same instances
--   - encoding: I_CQ, I_CC as maxima over measurement maps with an orthonormal register → sSup over POVMs with any finite number n of outcomes, the outcome written in the computational basis of Fin n; reason: the maximum is attained in finite dimension, so sSup is the paper's value; any other orthonormal register gives a unitarily equivalent state with the same entropies
--   - encoding: log of unspecified base in S(ρ) = −Tr ρ log ρ → QAlgorithms.vnEntropy, base 2; reason: every statement here is invariant under the base of the logarithm
--   - encoding: classical-classical: two orthonormal sets {|i⟩}, {|j⟩} and a joint distribution p_ij with ρ = Σ_ij p_ij |i⟩⟨i| ⊗ |j⟩⟨j| → IsClassicalClassical: Orthonormal families e : Fin k → EuclideanSpace ℂ a, f : Fin l → EuclideanSpace ℂ b, p ≥ 0 with Σ p = 1, ρ = Σ_ij p_ij pureDensity (e i) ⊗ₖ pureDensity (f j); reason: an orthonormal set of a finite-dimensional space is a finite family; p may vanish, so families and sets give the same states
-- source:
--   Piani, Horodecki & Horodecki, No-local-broadcasting theorem for quantum correlations, arXiv:0707.0848v2, p. 2, Theorem 1 (proof pp. 2–3)

import Mathlib
import Definitions.Def_NoLocalBroadcast_Broadcast_Model

namespace NoLocalBroadcast.Broadcast

open Matrix
open scoped Kronecker

/-- Theorem 1, p. 2: `I_CC(ρ) = I(ρ)` if and only if `ρ` is classical-classical. -/
theorem theorem_1 {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    (ρ : Matrix (a × b) (a × b) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    I_CC ρ = mutualInfo ρ ↔ IsClassicalClassical ρ := by sorry

end NoLocalBroadcast.Broadcast
