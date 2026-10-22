-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_fcn_spectrum
-- name    : NoiseAssistedTransport.FCN.fcn_spectrum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:09.767749+00:00
-- url     : https://prove2.me/theorems/8e405c8e-4a73-4853-853f-94996aaaa599
-- title:
--   §II.A, p. 4 — eigenstates of the FCN: |φ⟩ with E = J(N−1), |ψ_j⟩ = |1⟩ − |j⟩ with E = −J
-- statement:
--   Let $H$ be the Hamiltonian of the fully connected network of $N \ge 1$ sites with zero site energies and hopping $J$: $\langle i|H|j\rangle = J$ for distinct sites $i \ne j$, and all other entries zero. Let $|\phi\rangle = N^{-1/2}\sum_{j=1}^N |j\rangle$ and $|\psi_j\rangle = |1\rangle - |j\rangle$. Then
--
--   1. $H|\phi\rangle = J(N-1)\,|\phi\rangle$;
--   2. $H|\psi_j\rangle = -J\,|\psi_j\rangle$ for every $j = 2, \dots, N$;
--   3. every vector supported on the sites $1,\dots,N$ (zero on $|0\rangle$ and on the sink $|N+1\rangle$) is a linear combination of $|\phi\rangle$ and $|\psi_2\rangle,\dots,|\psi_N\rangle$.
--
--   So the eigenstates of the FCN consist of $|\phi\rangle$ with energy $J(N-1)$ and the $(N-1)$-fold degenerate level $-J$, which is spanned by the antisymmetric pair states $|\psi_j\rangle$. This spectrum is what the invariant-subspace analysis of §II.A is built on.
--
--   **Formalization Note** Vectors are functions `Fin (N + 2) → ℂ` and $H|v\rangle$ is `Matrix.mulVec`. Item 3 renders "the eigenstates of the FCN consist of" these states: the $N$ listed eigenvectors span the $N$-dimensional site space.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 4, §II.A

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- §II.A, p. 4: the eigenstates of the FCN Hamiltonian (`ω_j = 0`). -/
theorem fcn_spectrum (N : ℕ) (hN : 1 ≤ N) (J : ℝ) :
    hamiltonian N (fun _ => 0) J *ᵥ phiState N = ((J * ((N : ℝ) - 1) : ℝ) : ℂ) • phiState N ∧
    (∀ j ∈ Finset.Icc 2 N,
      hamiltonian N (fun _ => 0) J *ᵥ psiState N j = ((-J : ℝ) : ℂ) • psiState N j) ∧
    (∀ v : Fin (N + 2) → ℂ, v 0 = 0 → v ((N + 1 : ℕ) : Fin (N + 2)) = 0 →
      v ∈ Submodule.span ℂ (insert (phiState N) (psiState N '' Set.Icc 2 N))) := by sorry

end NoiseAssistedTransport.FCN
