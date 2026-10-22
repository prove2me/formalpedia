-- Prove2me | Theorems.Thm_NoiseAssistedTransport_FCN_eq_8_expansion
-- name    : NoiseAssistedTransport.FCN.eq_8_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:08.350025+00:00
-- url     : https://prove2.me/theorems/7759026f-0d0b-4ec2-8fd9-457946ee4884
-- title:
--   Eq. (8), p. 4 — expansion of |1⟩ in invariant and non-invariant states
-- statement:
--   For the fully connected network of $N \ge 2$ sites, with $|\phi\rangle = N^{-1/2}\sum_{j=1}^N |j\rangle$ and $|\psi_j\rangle = |1\rangle - |j\rangle$, the initially occupied site state expands as
--
--   $$|1\rangle = \frac{1}{N-1}\Bigl[\,\sum_{j=2}^{N-1}|\psi_j\rangle + \sqrt N\,|\phi\rangle - |N\rangle\Bigr].$$
--
--   The first sum lies in the invariant subspace (eigenstates of $H$ with no overlap with the sink-coupled site $N$); the remaining part $\sqrt N|\phi\rangle - |N\rangle$ is the component that the dynamics transfers to the sink. For $N = 2$ the first sum is empty.
-- source:
--   Caruso et al., Highly efficient energy excitation transfer in light-harvesting complexes, arXiv:0901.4454v2, p. 4, §II.A, Eq. (8); cf. p. 14, Eq. (A31)

import Mathlib
import Definitions.Def_NoiseAssistedTransport_FCN_Model
open scoped Matrix
open Fin.NatCast

namespace NoiseAssistedTransport.FCN

/-- Eq. (8), p. 4: `|1⟩ = (1/(N − 1)) [Σ_{j=2}^{N−1} |ψ_j⟩ + √N |φ⟩ − |N⟩]`. -/
theorem eq_8_expansion (N : ℕ) (hN : 2 ≤ N) :
    ket N 1 = ((1 / ((N : ℝ) - 1) : ℝ) : ℂ) •
      ((∑ j ∈ Finset.Icc 2 (N - 1), psiState N j) + ((Real.sqrt N : ℝ) : ℂ) • phiState N
        - ket N N) := by sorry

end NoiseAssistedTransport.FCN
