-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_heisenberg_update
-- name    : HeisenbergRep.Knill.heisenberg_update
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:59:29.098565+00:00
-- url     : https://prove2.me/theorems/a902385b-787d-4672-86e9-4d3eaedf1829
-- title:
--   Eqs. (1), (6): the Heisenberg update $UN|\psi\rangle=UNU^\dagger U|\psi\rangle$ and $N\mapsto UNU^\dagger$ is multiplicative
-- statement:
--   Let $U$ be a unitary $2^n\times2^n$ matrix, $M$ and $N$ any $2^n\times2^n$ matrices, and $|\psi\rangle\in\mathbb C^{2^n}$ any vector. Then
--
--   $$UN|\psi\rangle=\bigl(UNU^\dagger\bigr)\,U|\psi\rangle \qquad\text{and}\qquad U(MN)U^\dagger=\bigl(UMU^\dagger\bigr)\bigl(UNU^\dagger\bigr).$$
--
--   The first identity says that after the operation $U$, the operator $UNU^\dagger$ acts on the new state as $N$ acted on the old one; the second says that $N\mapsto UNU^\dagger$ is multiplicative, so it suffices to follow the images of a generating set.
--
--   Differences from the source:
--   - reading: apply the operator U to the computer → U ∈ Matrix.unitaryGroup (U†U = UU† = I); reason: (1) uses U†U = I; an operation applied to a quantum computer is unitary
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, Eq. (1), p. 3; Eq. (6), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace HeisenbergRep.Knill

open QAlgorithms
open scoped Matrix

/-- **Eqs. (1) and (6): the Heisenberg update `UN|ψ⟩ = UNU†U|ψ⟩`, and `N ↦ UNU†` is
multiplicative.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §2,
Eq. (1), p. 3: "Suppose we have a quantum computer in the state `|ψ⟩`, and we apply the operator
`U`. Then `UN|ψ⟩ = UNU†U|ψ⟩`"; Eq. (6), p. 4: "(2) is a multiplicative group homomorphism:
`MN → UMNU† = (UMU†)(UNU†)`".

For a unitary `2^n × 2^n` matrix `U`, any matrices `M`, `N` and any vector `ψ`:
`U (N ψ) = (U N U†)(U ψ)` and `U (M N) U† = (U M U†)(U N U†)`.

**Formalization Note.** `M` and `N` are arbitrary matrices and `ψ` an arbitrary vector (the paper
says "an arbitrary operation `N`"); `U ∈ Matrix.unitaryGroup` means `U† U = U U† = I`. -/
theorem heisenberg_update {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (M N : Matrix (Qubits n) (Qubits n) ℂ)
    (ψ : EuclideanSpace ℂ (Qubits n)) :
    act U (act N ψ) = act (U * N * Uᴴ) (act U ψ) ∧
      U * (M * N) * Uᴴ = (U * M * Uᴴ) * (U * N * Uᴴ) := by sorry

end HeisenbergRep.Knill
