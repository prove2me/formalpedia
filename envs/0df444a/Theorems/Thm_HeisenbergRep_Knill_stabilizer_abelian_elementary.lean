-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_stabilizer_abelian_elementary
-- name    : HeisenbergRep.Knill.stabilizer_abelian_elementary
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:49.019303+00:00
-- url     : https://prove2.me/theorems/e8a07d20-77d8-4696-9cfb-a3932424d286
-- title:
--   Eqs. (19)–(22): the stabilizer is Abelian, has phases $\pm1$, and is isomorphic to $(\mathbb Z_2)^k$
-- statement:
--   Let $\Psi\subseteq\mathbb C^{2^n}$ be a set of allowed inputs containing at least one nonzero vector, and let $S=\{M\in\mathcal P: M|\psi\rangle=|\psi\rangle \text{ for all }|\psi\rangle\in\Psi\}$ be its stabilizer. Then
--
--   1. $S$ is Abelian: $MN=NM$ for all $M,N\in S$;
--   2. every $M\in S$ is a Pauli operator $\pm P_1\otimes\cdots\otimes P_n$ with overall phase $+1$ or $-1$, and $M^2=I$;
--   3. there is $k\in\mathbb N$ with
--   $$S\cong(\mathbb Z_2)^k$$
--   as groups.
--
--   This is what makes a stabilizer a compact description of a state: it is an elementary Abelian 2-group, described by $k$ independent generators.
--
--   **Formalization Note** The isomorphism is a group isomorphism onto `Multiplicative (Fin k → ZMod 2)`. The paper's remark that $k$ is the number of fixed input qubits concerns its running example and is not part of the statement.
--
--   Differences from the source:
--   - reading: allowed inputs |ψ⟩ → vectors of ℂ^(2^n) (Ψ : Set), required to be states (nonzero); reason: with Ψ = ∅ or Ψ = {0}, S is the whole non-Abelian Pauli group
--   - generalization: every allowed input is a (nonzero) state → Ψ contains at least one nonzero vector; reason: the conclusions only use one nonzero stabilized vector; a set of states satisfies this when nonempty
--   - encoding: S is isomorphic to (Z2)^k → Nonempty (stabilizerOf Ψ ≃* Multiplicative (Fin k → ZMod 2)); reason: group isomorphism, same statement
--   - encoding: operators in P which have an overall phase of ±1, and which square to +1 → M = P.toMatrix for a PauliString with phase 0 or 2, and M * M = 1; reason: same statement
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §4, Eqs. (19)–(22), p. 9

import Mathlib
import Definitions.Def_HeisenbergRep_Knill_stabilizerOf

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer

/-- **Eqs. (19)–(22): the stabilizer is an Abelian group of `±1`-phase operators squaring to `+1`,
isomorphic to `(ℤ₂)^k`.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §4,
p. 9: "`S = {M ∈ P such that M|ψ⟩ = |ψ⟩ for all allowed inputs |ψ⟩}` (19) … The stabilizer is
always an Abelian group: If `M, N ∈ S`, then `MN|ψ⟩ = |ψ⟩` (20) `NM|ψ⟩ = |ψ⟩` (21)
`[M, N]|ψ⟩ = 0` (22). … Therefore, any stabilizer is composed of operators in `P` which have an
overall phase of `±1`, and which square to `+1`. It follows that `S` is isomorphic to `(Z_2)^k` for
some `k`."

Let `Ψ` be a set of vectors of `ℂ^{2^n}` (the allowed inputs) containing at least one nonzero
vector, and let `S = stabilizerOf Ψ` be its stabilizer (19). Then
1. `S` is commutative: `MN = NM` for all `M, N ∈ S`;
2. every `M ∈ S` is a Pauli operator `±P_1 ⊗ ⋯ ⊗ P_n` with overall phase `+1` or `−1`, and
   `M² = I`;
3. `S ≅ (ℤ₂)^k` as groups, for some `k ∈ ℕ`.

**Formalization Note.** "Allowed inputs `|ψ⟩`" are states, i.e. nonzero vectors; the statement
only needs one nonzero allowed input (if `Ψ = ∅` or `Ψ = {0}`, `S` is the whole non-Abelian
Pauli group). `(ℤ₂)^k` is `Multiplicative (Fin k → ZMod 2)`; the isomorphism is a group
isomorphism `≃*`. The paper's remark that `k` is "exactly the number of input qubits that are
fixed" concerns its running example and is not part of the statement. -/
theorem stabilizer_abelian_elementary {n : ℕ} (Ψ : Set (EuclideanSpace ℂ (Qubits n)))
    (hΨ : ∃ ψ ∈ Ψ, ψ ≠ 0) :
    (∀ M ∈ stabilizerOf Ψ, ∀ N ∈ stabilizerOf Ψ, M * N = N * M) ∧
    (∀ M ∈ stabilizerOf Ψ, (∃ P : PauliString n, (P.phase = 0 ∨ P.phase = 2) ∧
        (M : Matrix (Qubits n) (Qubits n) ℂ) = P.toMatrix) ∧ M * M = 1) ∧
    ∃ k : ℕ, Nonempty (stabilizerOf Ψ ≃* Multiplicative (Fin k → ZMod 2)) := by sorry

end HeisenbergRep.Knill
