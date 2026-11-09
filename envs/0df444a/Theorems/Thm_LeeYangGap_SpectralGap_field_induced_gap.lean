-- Prove2me | Theorems.Thm_LeeYangGap_SpectralGap_field_induced_gap
-- name    : LeeYangGap.SpectralGap.field_induced_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:32.972035+00:00
-- url     : https://prove2.me/theorems/4664b2fb-d2e5-4148-83f1-c13bedb34921
-- title:
--   Theorem 11 — Spectral gap: unique ground state and gap at least h/4
-- statement:
--   Let $H$ be any Lee–Yang Hamiltonian on a finite nonempty system of $n$ qubits, with all five real bond coefficients satisfying Definition 1, and let $h>0$. For $H_h=H-h\sum_iZ_i$, the ground state is nondegenerate and the eigenvalues in nondecreasing order, counted with multiplicity, satisfy
--   $$E_1-E_0\ge\frac h4.$$
--   Equivalently, a normalized ground eigenvector exists, every vector in its eigenspace is its scalar multiple, and every other eigenvalue is at least $E_0+h/4$. The theorem is uniform in the graph, system size, coupling strengths and both cross couplings. It supplies both the simplicity and gap conclusions; no spectral separation is assumed.
--
--   Differences from the source:
--   - encoding: finite qubit Hilbert space and site indices → complex matrices indexed by Fin n → Fin 2, with finite ordered bond lists; reason: the computational basis and bond order are explicit; arbitrary finite graphs are represented, with no coefficient restriction added
--   - encoding: nondegenerate ground state and E₁−E₀≥h/4, eigenvalues counted with multiplicity → normalized ground eigenvector, one-dimensional ground eigenspace, and every other eigenvalue at least E₀+h/4; reason: the Hermitian spectral theorem makes the two formulations equivalent, including degeneracy
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, Theorem 11, printed/PDF p. 12

import Mathlib
import Definitions.Def_LeeYangGap_SpectralGap_Analytic
open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap

/-- Rayudu–Takahashi, STOC 2027 submission #575; source index in items.yaml. -/
theorem field_induced_gap {n : ℕ} (hn : 0 < n) (B : System n) (hLY : IsLeeYang B)
    (h : ℝ) (hh : 0 < h) :
    HasGroundGap (fieldHamiltonian B h) (h/4) := by sorry
end LeeYangGap.SpectralGap
