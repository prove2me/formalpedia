-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_measurement_correction
-- name    : HeisenbergRep.Knill.measurement_correction
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:59:28.076497+00:00
-- url     : https://prove2.me/theorems/c743b7e1-0607-44f6-aa3c-5e80a8cde194
-- title:
--   Eqs. (35)–(36): $MP_-M^\dagger=P_+$, so correcting by $M$ after the result $-1$ gives $P_+|\psi\rangle$
-- statement:
--   Let $M$ be an element of the $n$-qubit Pauli group and $A$ a $2^n\times2^n$ matrix anticommuting with $M$ ($MA=-AM$), and let $P_\pm=\tfrac12(I\pm A)$ be the operators performed by a measurement of $A$ with result $\pm1$. Then
--
--   1. $$MP_-M^\dagger=P_+ ;$$
--   2. for every vector $|\psi\rangle$ with $M|\psi\rangle=|\psi\rangle$: $\;M\,P_-|\psi\rangle=P_+|\psi\rangle$.
--
--   Hence, if $M$ is in the stabilizer of the state, applying $M$ whenever the result is $-1$ always yields the state $P_+|\psi\rangle$; this is the correction step of the measurement rule.
--
--   Differences from the source:
--   - generalization: A ∈ P anticommuting with M → A any 2^n × 2^n matrix with MA = −AM; reason: (36) uses only the anticommutation and MM† = I
--   - generalization: M ∈ S (the stabilizer of the state) → M any Pauli-group element; Mψ = ψ assumed in clause 2 only; reason: clause 1 does not use Mψ = ψ; with M ∈ S both clauses give the paper's
--   - encoding: we always get the state P+|ψ⟩ (normalized) → M(P−ψ) = P+ψ for the unnormalized vectors; reason: M is unitary, so ‖P−ψ‖ = ‖P+ψ‖ and the normalized states agree
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §7, Eqs. (35)–(36), p. 15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

namespace HeisenbergRep.Knill

open QAlgorithms
open scoped Matrix

/-- **Eqs. (35)–(36): `M P₋ M† = P₊`, so applying `M` after the result `−1` gives `P₊|ψ⟩`.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §7,
p. 15: "Suppose we wish to measure an operator `A ∈ P` which anticommutes with some element
`M ∈ S`. The measurement performs one of the operators `P± = ½(I ± A)`, (35) depending on whether
the measurement result is `±1`. But `MP₋M† = ½M(I − A)M† = ½(I + A)MM† = P₊`. (36) Therefore, by
applying `M` whenever the measurement result is `−1`, we can ensure that we always get the state
`P₊|ψ⟩`."

Let `M` be an element of the `n`-qubit Pauli group and `A` a `2^n × 2^n` matrix with `MA = −AM`,
and let `P± = ½(I ± A)`. Then
1. `M P₋ M† = P₊`;
2. for every vector `ψ` with `Mψ = ψ`: `M (P₋ ψ) = P₊ ψ`.

**Formalization Note.** The paper has `A ∈ P`; here `A` is any matrix anticommuting with `M` (a
generalization: neither clause uses more). "`M ∈ S`" enters only through `Mψ = ψ` in clause 2.
`P±` are written `(2⁻¹ : ℂ) • (1 ± A)`. -/
theorem measurement_correction {n : ℕ} (M : Matrix.unitaryGroup (Qubits n) ℂ)
    (hM : M ∈ pauliGroup n) (A : Matrix (Qubits n) (Qubits n) ℂ)
    (hMA : (M : Matrix (Qubits n) (Qubits n) ℂ) * A = -(A * (M : Matrix (Qubits n) (Qubits n) ℂ))) :
    (M : Matrix (Qubits n) (Qubits n) ℂ) * ((2⁻¹ : ℂ) • (1 - A)) *
        (M : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = (2⁻¹ : ℂ) • (1 + A) ∧
    ∀ ψ : EuclideanSpace ℂ (Qubits n), act (M : Matrix (Qubits n) (Qubits n) ℂ) ψ = ψ →
      act (M : Matrix (Qubits n) (Qubits n) ℂ) (act ((2⁻¹ : ℂ) • (1 - A)) ψ) =
        act ((2⁻¹ : ℂ) • (1 + A)) ψ := by sorry

end HeisenbergRep.Knill
