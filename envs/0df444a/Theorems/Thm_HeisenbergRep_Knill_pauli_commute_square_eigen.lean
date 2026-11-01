-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_pauli_commute_square_eigen
-- name    : HeisenbergRep.Knill.pauli_commute_square_eigen
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:30.576985+00:00
-- url     : https://prove2.me/theorems/a6fa121b-784d-4d88-a6b8-2998d2434c63
-- title:
--   p. 9: Pauli operators commute or anticommute, square to $\pm1$, and have eigenvalues $\pm1$ or $\pm i$
-- statement:
--   Let $P=i^cP_1\otimes\cdots\otimes P_n$ and $Q$ be $n$-qubit Pauli operators ($c\in\mathbb Z/4$, $P_q\in\{I,X,Y,Z\}$). Then
--
--   1. $PQ=QP$ or $PQ=-QP$;
--   2. if the overall phase $i^c$ of $P$ is $\pm1$, then $P^2=I$;
--   3. if the overall phase of $P$ is $\pm i$, then $P^2=-I$;
--   4. if $Pv=\mu v$ for a nonzero vector $v$, then $\mu\in\{1,-1\}$ when the phase of $P$ is $\pm1$, and $\mu\in\{i,-i\}$ when it is $\pm i$.
--
--   These facts underlie the stabilizer formalism: they make every stabilizer Abelian and composed of Hermitian operators.
--
--   Differences from the source:
--   - encoding: an element of the Pauli group P → a PauliString n (phase exponent c ∈ ZMod 4) and its matrix toMatrix; reason: P is exactly the set of these matrices
--   - reading: the operators that square to −1 have imaginary eigenvalues → every eigenvalue is i or −i; reason: the eigenvalues of a matrix with square −I are ±i
--   - reading: the operators that square to +1 have eigenvalues ±1 → every eigenvalue is +1 or −1; reason: I has only the eigenvalue +1, so "both occur" would be false
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §4, p. 9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

/-- **Elements of the Pauli group commute or anticommute, square to `±1`, and have eigenvalues
`±1` or `±i`.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §4,
p. 9: "Any two elements of `P` either commute or anticommute … In addition, all elements of `P`
square to `±1` (operators with an overall phase of `±1` square to `+1`, operators with an overall
phase of `±i` square to `−1`). The operators that square to `−1` have imaginary eigenvalues, while
the operators that square to `+1` have eigenvalues `±1`."

For all `n`-qubit Pauli operators `P = i^c P_1 ⊗ ⋯ ⊗ P_n` and `Q`:
1. `PQ = QP` or `PQ = −QP`;
2. if the phase `i^c` of `P` is `±1`, then `P² = I`;
3. if the phase of `P` is `±i`, then `P² = −I`;
4. every eigenvalue `μ` of `P` (with a nonzero eigenvector `v`, `Pv = μv`) is `±1` when the
   phase is `±1`, and `±i` when the phase is `±i`.

**Formalization Note.** An element of the Pauli group is written as a `PauliString n` (phase
exponent `c ∈ ℤ/4`, so phase `±1` is `c ∈ {0, 2}` and phase `±i` is `c ∈ {1, 3}`) with matrix
`PauliString.toMatrix`. "Imaginary eigenvalues" is read as "eigenvalues in `{i, −i}`", and
"eigenvalues `±1`" as "every eigenvalue is `+1` or `−1`" (the identity has only the eigenvalue
`+1`). -/
theorem pauli_commute_square_eigen {n : ℕ} (P Q : PauliString n) :
    (P.toMatrix * Q.toMatrix = Q.toMatrix * P.toMatrix ∨
      P.toMatrix * Q.toMatrix = -(Q.toMatrix * P.toMatrix)) ∧
    ((P.phase = 0 ∨ P.phase = 2) → P.toMatrix ^ 2 = 1) ∧
    ((P.phase = 1 ∨ P.phase = 3) → P.toMatrix ^ 2 = -1) ∧
    ∀ (v : Qubits n → ℂ) (μ : ℂ), v ≠ 0 → P.toMatrix *ᵥ v = μ • v →
      ((P.phase = 0 ∨ P.phase = 2) → μ = 1 ∨ μ = -1) ∧
      ((P.phase = 1 ∨ P.phase = 3) → μ = Complex.I ∨ μ = -Complex.I) := by sorry

end HeisenbergRep.Knill
