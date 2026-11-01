-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_table1_clifford_generators
-- name    : HeisenbergRep.Knill.table1_clifford_generators
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:38.83936+00:00
-- url     : https://prove2.me/theorems/e0033a37-2106-497d-8a3e-c98b9096f742
-- title:
--   Table 1, Eqs. (7)–(9): $R$, $P$ and CNOT are Clifford gates, with their images of $X$ and $Z$, and generate the Clifford group (corrected: up to a global phase)
-- statement:
--   Let $R=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ (Hadamard), $P=\begin{pmatrix}1&0\\0&i\end{pmatrix}$ (phase gate) and CNOT$|j\rangle|k\rangle=|j\rangle|j+k \bmod 2\rangle$ (first qubit the control), and let $X,Y,Z$ be the Pauli matrices with $Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$.
--
--   1. The conjugation identities of Table 1 hold:
--   $$RXR^\dagger=Z,\quad RZR^\dagger=X,\quad PXP^\dagger=Y,\quad PZP^\dagger=Z,$$
--   $$\mathrm{CNOT}(X\otimes I)\mathrm{CNOT}^\dagger=X\otimes X,\quad \mathrm{CNOT}(I\otimes X)\mathrm{CNOT}^\dagger=I\otimes X,$$
--   $$\mathrm{CNOT}(Z\otimes I)\mathrm{CNOT}^\dagger=Z\otimes I,\quad \mathrm{CNOT}(I\otimes Z)\mathrm{CNOT}^\dagger=Z\otimes Z.$$
--   2. For every $n$, every qubit $j$ and every pair of distinct qubits $j\neq k$ of an $n$-qubit computer, the gates $R(j)$, $P(j)$ and $\mathrm{CNOT}(j\to k)$ (control $j$, target $k$), as $2^n\times2^n$ matrices, are unitary and belong to the Clifford group $N(\mathcal P)$, the normalizer of the Pauli group in $U(2^n)$.
--
--   3. For every $n$, every element $U$ of the Clifford group $N(\mathcal P)$ is a scalar multiple of a finite product of gates $R(j)$, $P(j)$ and $\mathrm{CNOT}(j\to k)$: $U=c\,G_1G_2\cdots G_m$ for some $c\in\mathbb C$.
--
--   These are the generators the paper uses to describe Clifford networks.
--
--   **Formalization Note** The $n$-qubit gates are the one- and two-qubit matrices placed on the chosen wires and tensored with the identity elsewhere (`embedOp`). The ket form of (7) omits the factor $1/\sqrt2$ that its matrix carries; the matrix is used.
--
--   Differences from the source:
--   - reading: the Clifford group contains R, P and CNOT, applied as R(j), P(j), CNOT(j → k) → for every n, j and k ≠ j, the embedded gate is unitary and lies in Clifford.normalizer n; reason: p. 4 applies the gates "to arbitrary qubits or pairs of qubits"; n = 1, 2 give the bare gates
--   - reading: (7): R|j⟩ = |0⟩ + (−1)^j|1⟩ and R = (1/√2)[[1, 1], [1, −1]] → R = hadamard, the normalized matrix; reason: the ket form omits the 1/√2 of the matrix; only the matrix is unitary
--   - encoding: X ⊗ I, I ⊗ Z, … on two qubits, control first → Kronecker products pauliX ⊗ₖ 1, … on Bool × Bool, first factor = control of QAlgorithms.cnot; reason: same matrices
--   - correction: R, P, and CNOT, applied to arbitrary qubits or pairs of qubits, generate the full Clifford group C (p. 4; Table 1 caption "Generators of the Clifford group") → every U ∈ Clifford.normalizer n equals c • (a finite product of R(j), P(j), CNOT(j → k)) for some c ∈ ℂ; reason: literally false: for n = 1, U = e^{iπ/8} I lies in N(P) ⊆ U(2), but R and P generate a finite group (192 elements) whose scalar elements are the powers of e^{iπ/4}, so U is not a product of them; the generation holds up to a global phase
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §3, Eqs. (7)–(9), p. 4; Table 1, p. 5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords

namespace HeisenbergRep.Knill

open QAlgorithms
open scoped Matrix Kronecker

/-- **Table 1 with Eqs. (7)–(9): `R`, `P` and CNOT are Clifford gates, with their induced
transformations of the Pauli matrices, and they generate the Clifford group (corrected: up to a
global phase).**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §3,
p. 4: "the Clifford group contains the single-qubit Hadamard transform R: … `R = (1/√2)[[1, 1],
[1, −1]]` (7). Another element is the phase gate P: … `P = [[1, 0], [0, i]]` (8). It also contains
the controlled-NOT (CNOT) gate … `CNOT|j⟩|k⟩ = |j⟩|j + k mod 2⟩` (9). The first qubit is called
the control qubit and the second is the target qubit. In fact, R, P, and CNOT, applied to arbitrary
qubits or pairs of qubits, generate the full Clifford group C"; Table 1, p. 5: "R: `X → Z`, `Z → X`;
P: `X → Y`, `Z → Z`; CNOT: `X ⊗ I → X ⊗ X`, `I ⊗ X → I ⊗ X`, `Z ⊗ I → Z ⊗ I`, `I ⊗ Z → Z ⊗ Z`".

The statement has two parts.
1. The conjugation identities of Table 1: `R X R† = Z`, `R Z R† = X`, `P X P† = Y`,
   `P Z P† = Z`, and, on two qubits with the control first, `CNOT (X ⊗ I) CNOT† = X ⊗ X`,
   `CNOT (I ⊗ X) CNOT† = I ⊗ X`, `CNOT (Z ⊗ I) CNOT† = Z ⊗ I`, `CNOT (I ⊗ Z) CNOT† = Z ⊗ Z`.
2. For every `n`, the gates `R(j)` and `P(j)` (applied to qubit `j`) and `CNOT(j → k)` (control
   `j`, target `k ≠ j`), as `2^n × 2^n` matrices, are unitary and lie in the Clifford group
   `N(P)`, the normalizer of the Pauli group in `U(2^n)`.
3. For every `n`, every element `U` of the Clifford group `N(P)` is a scalar `c` times a finite
   product of gates `R(j)`, `P(j)`, `CNOT(j → k)`.

**Formalization Note.** `R = hadamard`, `P = phaseS = diag(1, i)`, `CNOT = QAlgorithms.cnot` on
`Bool × Bool` (first component = control); `X ⊗ I` is the Kronecker product `pauliX ⊗ₖ 1`, first
factor = first qubit; `Y = pauliY = [[0, −i], [i, 0]] = σ_y` (p. 3, footnote 1). The `n`-qubit
gates are `embedOp` of the one- and two-qubit matrices on the wires `wire1 j` and `wire2 j k`
(gate wire `0` = control). The ket form of (7), "`R|j⟩ = |0⟩ + (−1)^j|1⟩`", omits the factor
`1/√2` that the matrix in (7) carries; the matrix is used. The table's last row (measurement plus a
classically controlled operation) is notation, not a claim. (Correction) The page and the caption
of Table 1 say that `R`, `P`, CNOT "generate the full Clifford group"; literally this is false,
since `N(P) ⊆ U(2^n)` contains every scalar `e^{iθ} I`, while these gates generate a finite group.
Part 3 states the generation up to a global phase `c`, which is the true content (the phase is
not observable). -/
theorem table1_clifford_generators :
    (hadamard * pauliX * hadamardᴴ = pauliZ ∧ hadamard * pauliZ * hadamardᴴ = pauliX) ∧
    (phaseS * pauliX * phaseSᴴ = pauliY ∧ phaseS * pauliZ * phaseSᴴ = pauliZ) ∧
    (QAlgorithms.cnot * (pauliX ⊗ₖ (1 : Matrix Bool Bool ℂ)) * QAlgorithms.cnotᴴ =
        pauliX ⊗ₖ pauliX ∧
      QAlgorithms.cnot * ((1 : Matrix Bool Bool ℂ) ⊗ₖ pauliX) * QAlgorithms.cnotᴴ =
        (1 : Matrix Bool Bool ℂ) ⊗ₖ pauliX ∧
      QAlgorithms.cnot * (pauliZ ⊗ₖ (1 : Matrix Bool Bool ℂ)) * QAlgorithms.cnotᴴ =
        pauliZ ⊗ₖ (1 : Matrix Bool Bool ℂ) ∧
      QAlgorithms.cnot * ((1 : Matrix Bool Bool ℂ) ⊗ₖ pauliZ) * QAlgorithms.cnotᴴ =
        pauliZ ⊗ₖ pauliZ) ∧
    ∀ n : ℕ,
      (∀ j : Fin n, ∃ hU : embedOp (Gate.ofMatrix1 hadamard).mat (Stabilizer.wire1 j) ∈
          Matrix.unitaryGroup (Qubits n) ℂ,
        (⟨_, hU⟩ : Matrix.unitaryGroup (Qubits n) ℂ) ∈ Clifford.normalizer n) ∧
      (∀ j : Fin n, ∃ hU : embedOp (Gate.ofMatrix1 phaseS).mat (Stabilizer.wire1 j) ∈
          Matrix.unitaryGroup (Qubits n) ℂ,
        (⟨_, hU⟩ : Matrix.unitaryGroup (Qubits n) ℂ) ∈ Clifford.normalizer n) ∧
      (∀ (j k : Fin n) (hjk : j ≠ k),
        ∃ hU : embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (Stabilizer.wire2 j k hjk) ∈
          Matrix.unitaryGroup (Qubits n) ℂ,
        (⟨_, hU⟩ : Matrix.unitaryGroup (Qubits n) ℂ) ∈ Clifford.normalizer n) ∧
      (∀ U ∈ Clifford.normalizer n, ∃ (c : ℂ) (gs : List (Matrix (Qubits n) (Qubits n) ℂ)),
        (∀ g ∈ gs,
          (∃ j : Fin n, g = embedOp (Gate.ofMatrix1 hadamard).mat (Stabilizer.wire1 j)) ∨
          (∃ j : Fin n, g = embedOp (Gate.ofMatrix1 phaseS).mat (Stabilizer.wire1 j)) ∨
          (∃ (j k : Fin n) (hjk : j ≠ k),
            g = embedOp (Gate.ofMatrix2 QAlgorithms.cnot).mat (Stabilizer.wire2 j k hjk))) ∧
        (U : Matrix (Qubits n) (Qubits n) ℂ) = c • gs.prod) := by sorry

end HeisenbergRep.Knill
