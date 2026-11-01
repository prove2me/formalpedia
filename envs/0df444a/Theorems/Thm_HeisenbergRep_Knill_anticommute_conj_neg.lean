-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_anticommute_conj_neg
-- name    : HeisenbergRep.Knill.anticommute_conj_neg
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:45.364371+00:00
-- url     : https://prove2.me/theorems/ad404ee6-a367-47ce-999e-3530622a956f
-- title:
--   Eq. (30): conjugating by an anticommuting Pauli operator negates, $EME^\dagger=-M$
-- statement:
--   Let $E$ be an element of the $n$-qubit Pauli group and $M$ a $2^n\times2^n$ matrix that anticommutes with $E$, $\{E,M\}=EM+ME=0$. Then
--
--   $$E(M)=EME^\dagger=-M .$$
--
--   So applying a Pauli operator $E$ flips the sign of every operator it anticommutes with; the paper uses this to change the signs of stabilizer generators.
--
--   Differences from the source:
--   - generalization: M ∈ P (the stabilizer generators X ⊗ X, Z ⊗ Z) → M any 2^n × 2^n matrix with EM = −ME; reason: the identity uses only EE† = I; taking M ∈ P gives (30)
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §5, Eq. (30), p. 11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

namespace HeisenbergRep.Knill

open QAlgorithms
open scoped Matrix

/-- **Eq. (30): conjugating by an anticommuting Pauli operator negates.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §5,
Eq. (30), p. 11: "any operator `E ∈ P` that anticommutes with both `X ⊗ X` and `Z ⊗ Z` would work:
if `{E, M} = 0`, then `E(M) = EME† = −EE†M = −M`."

For every element `E` of the `n`-qubit Pauli group and every `2^n × 2^n` matrix `M` with
`EM = −ME` (`{E, M} = 0`): `E M E† = −M`.

**Formalization Note.** The paper has `M ∈ P`; here `M` is any matrix (a generalization: the
identity uses only that `E` is unitary). The Pauli group is `QAlgorithms.pauliGroup n`, a subgroup
of `U(2^n)`. -/
theorem anticommute_conj_neg {n : ℕ} (E : Matrix.unitaryGroup (Qubits n) ℂ)
    (hE : E ∈ pauliGroup n) (M : Matrix (Qubits n) (Qubits n) ℂ)
    (hEM : (E : Matrix (Qubits n) (Qubits n) ℂ) * M = -(M * (E : Matrix (Qubits n) (Qubits n) ℂ))) :
    (E : Matrix (Qubits n) (Qubits n) ℂ) * M * (E : Matrix (Qubits n) (Qubits n) ℂ)ᴴ = -M := by sorry

end HeisenbergRep.Knill
