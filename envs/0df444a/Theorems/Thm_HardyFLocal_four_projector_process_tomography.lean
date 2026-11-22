-- Prove2me | Theorems.Thm_HardyFLocal_four_projector_process_tomography
-- name    : HardyFLocal.four_projector_process_tomography
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:31:26.039831+00:00
-- url     : https://prove2.me/theorems/981f14ba-89b9-4ae6-9cd5-f960ad547d69
-- title:
--   Four projectors give a separating set of single-qubit process tests
-- statement:
--   There are four positive semidefinite qubit projectors $P_i$ of trace one, each with positive semidefinite complement, such that for every two Hermiticity-preserving complex-linear maps $\Phi,\Psi$ on the qubit matrix algebra,
--   $$\Phi=\Psi\quad\Longleftrightarrow\quad \operatorname{Re}\operatorname{Tr}(P_j\Phi(P_i))=\operatorname{Re}\operatorname{Tr}(P_j\Psi(P_i))\text{ for all }i,j.$$
--   The same four projectors serve as density matrices on input and as binary measurement effects on output. These sixteen real evaluations separate the maps used in the single-wire interior tomography argument.
-- source:
--   Supporting lemma for the interior fiduciality milestone in the formalization of Lucien Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, section 5. https://arxiv.org/abs/0804.0054

import Definitions.Def_HardyFLocal_Superoperator
open scoped Matrix ComplexOrder

namespace HardyFLocal

theorem four_projector_process_tomography :
    ∃ P : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i, (P i).PosSemidef ∧ (1 - P i).PosSemidef ∧ (P i).trace = 1 ∧ P i * P i = P i) ∧
      ∀ Φ ∈ hpMaps (Fin 2), ∀ Ψ ∈ hpMaps (Fin 2),
        (∀ i j, (P j * Φ (P i)).trace.re = (P j * Ψ (P i)).trace.re) ↔ Φ = Ψ := by sorry

end HardyFLocal
