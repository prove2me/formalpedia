-- Prove2me | Theorems.Thm_HeisenbergRep_Knill_measurement_update
-- name    : HeisenbergRep.Knill.measurement_update
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:31.80886+00:00
-- url     : https://prove2.me/theorems/86ec1b38-af28-4899-9380-16a9365292f2
-- title:
--   p. 15, rules 1–4: the stabilizer and the $\bar X$, $\bar Z$ operators after measuring $A$
-- statement:
--   Let $|\psi\rangle\neq0$, let $S$ be a set of Pauli-group elements with $N|\psi\rangle=|\psi\rangle$ for all $N\in S$, let $A=\pm P_1\otimes\cdots\otimes P_n$ be a Pauli operator with phase $\pm1$, and let $M\in S$ anticommute with $A$. Put $|\psi'\rangle=P_+|\psi\rangle=\tfrac12(I+A)|\psi\rangle$, the state after the result $+1$, or after the result $-1$ and the correction by $M$. Then
--
--   1. $|\psi'\rangle\neq0$;
--   2. $A|\psi'\rangle=|\psi'\rangle$ ($A$ joins the new stabilizer $S'$);
--   3. $M|\psi'\rangle\neq|\psi'\rangle$ ($M$ leaves);
--   4. every $N\in S$ commuting with $A$ satisfies $N|\psi'\rangle=|\psi'\rangle$;
--   5. every $N\in S$ anticommuting with $A$ satisfies $N|\psi'\rangle\neq|\psi'\rangle$, $MN|\psi'\rangle=|\psi'\rangle$, and $MN$ commutes with $A$;
--   6. every Pauli operator $L$ commuting with every element of $S$ and anticommuting with $A$ (an $\bar X_j$ or $\bar Z_j$) has $ML$ commuting with $A$, and $ML|\varphi\rangle=L|\varphi\rangle$ for every $|\varphi\rangle$ fixed by all of $S$.
--
--   These are the rules by which the Heisenberg representation updates a stabilizer description under a Pauli measurement: identify $M$, remove it, add $A$, and replace each anticommuting $N$ (generator or logical operator) by $MN$.
--
--   Differences from the source:
--   - reading: measure an operator A ∈ P → A a PauliString with phase exponent 0 or 2 (A = ±P, Hermitian); reason: for phase ±i, ½(I + A) is not a projector and clause 2 fails (A = iZ, ψ = |+⟩, S = {I, X}, M = X)
--   - reading: the state |ψ⟩ → ψ ≠ 0; reason: a state is a nonzero vector
--   - generalization: S the stabilizer, N running over its generators → S any set of Pauli-group elements fixing ψ, N over all of S; reason: the stabilizer and any generating set of it are such sets
--   - encoding: P+|ψ⟩ is in S′, A ∈ S′, M ∉ S′, N ∈ S′ → statements Aψ′ = ψ′, Mψ′ ≠ ψ′, Nψ′ = ψ′ about the unnormalized ψ′ = ½(I + A)ψ; reason: fixing a vector is invariant under nonzero scaling, and clause 1 gives ψ′ ≠ 0
--   - reading: X̄_j, Z̄_j; MX̄_j "acts the same way" → L ∈ pauliGroup n commuting with every element of S; (ML)φ = Lφ for every φ fixed by S; reason: p. 9: the X̄, Z̄ are operators that commute with S; p. 15: operators are equivalent up to multiplication by stabilizer elements
-- source:
--   Gottesman, The Heisenberg Representation of Quantum Computers, arXiv:quant-ph/9807006v1, §7, p. 15 (rules 1–4 and the two preceding paragraphs)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QECC

namespace HeisenbergRep.Knill

open QAlgorithms QAlgorithms.Stabilizer
open scoped Matrix

/-- **The stabilizer after measuring `A` (rules 1–4): `A` enters, `M` leaves, an anticommuting `N`
becomes `MN`, and `X̄_j` becomes `MX̄_j`.**
Gottesman, *The Heisenberg Representation of Quantum Computers*, arXiv:quant-ph/9807006v1, §7,
p. 15: "The state `P₊|ψ⟩` will always be in a `+1` eigenstate of `A`, so `A` is a member of the
new stabilizer `S′`. `M`, on the other hand, will not be in `S′`. The other generators will be in
`S′` if they commute with `A` … if `N ∈ S` does not commute with `A`, `N ∉ S′`; but `MN` does
commute with `A`, so `MN ∈ S′`. … even if `X̄_j` does not commute with `A`, `MX̄_j` does, and acts
the same way. … 1. Identify `M ∈ S` satisfying `{M, A} = 0`. 2. Remove `M` from the stabilizer
3. Add `A` to the stabilizer 4. For each `N`, where `N` runs over the other generators of `S` and
the `X̄` and `Z̄` operators, leave `N` alone if `[N, A] = 0`, and replace `N` with `MN` if
`{N, A} = 0`."

Let `ψ ≠ 0` be a vector of `ℂ^{2^n}`, `S` a set of elements of the Pauli group with `Nψ = ψ` for
every `N ∈ S`, `A = ±P_1 ⊗ ⋯ ⊗ P_n` a Pauli operator with phase `±1`, and `M ∈ S` with `MA = −AM`.
Let `ψ′ = P₊ψ = ½(I + A)ψ` be the (unnormalized) state after the measurement result `+1`, or
after the result `−1` and the correction by `M`. Then
1. `ψ′ ≠ 0`;
2. `Aψ′ = ψ′` (`A ∈ S′`);
3. `Mψ′ ≠ ψ′` (`M ∉ S′`);
4. every `N ∈ S` with `NA = AN` satisfies `Nψ′ = ψ′`;
5. every `N ∈ S` with `NA = −AN` satisfies `Nψ′ ≠ ψ′`, `(MN)ψ′ = ψ′`, and `MN` commutes with
   `A`;
6. every Pauli operator `L` that commutes with every element of `S` and anticommutes with `A` (an
   `X̄_j` or `Z̄_j`) has `ML` commuting with `A` and `(ML)φ = Lφ` for every `φ` fixed by every
   element of `S`.

**Formalization Note.** `A` is a `PauliString` with phase exponent `0` or `2` (Hermitian `A`): for
phase `±i`, `½(I + A)` is not a projector and clause 2 fails (`A = iZ`, `ψ = |+⟩`, `S = {I, X}`,
`M = X`). `S` is any set of Pauli-group elements stabilizing `ψ` (for instance the stabilizer or a
generating set), so "the other generators of `S`" are covered by "every `N ∈ S`". "Acts the same
way" is read as equality on the states fixed by `S`. -/
theorem measurement_update {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : ψ ≠ 0)
    (S : Set (Matrix.unitaryGroup (Qubits n) ℂ)) (hSP : S ⊆ pauliGroup n)
    (hSψ : ∀ N ∈ S, act (N : Matrix (Qubits n) (Qubits n) ℂ) ψ = ψ)
    (A₀ : PauliString n) (hA₀ : A₀.phase = 0 ∨ A₀.phase = 2)
    (M : Matrix.unitaryGroup (Qubits n) ℂ) (hMS : M ∈ S)
    (hMA : (M : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
      -(A₀.toMatrix * (M : Matrix (Qubits n) (Qubits n) ℂ))) :
    let ψ' := act ((2⁻¹ : ℂ) • (1 + A₀.toMatrix)) ψ
    ψ' ≠ 0 ∧
    act A₀.toMatrix ψ' = ψ' ∧
    act (M : Matrix (Qubits n) (Qubits n) ℂ) ψ' ≠ ψ' ∧
    (∀ N ∈ S, (N : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        A₀.toMatrix * (N : Matrix (Qubits n) (Qubits n) ℂ) →
      act (N : Matrix (Qubits n) (Qubits n) ℂ) ψ' = ψ') ∧
    (∀ N ∈ S, (N : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        -(A₀.toMatrix * (N : Matrix (Qubits n) (Qubits n) ℂ)) →
      act (N : Matrix (Qubits n) (Qubits n) ℂ) ψ' ≠ ψ' ∧
      act ((M * N : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) ψ' = ψ' ∧
      ((M * N : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        A₀.toMatrix * ((M * N : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ)) ∧
    (∀ L ∈ pauliGroup n, (∀ N ∈ S, L * N = N * L) →
      (L : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
        -(A₀.toMatrix * (L : Matrix (Qubits n) (Qubits n) ℂ)) →
      ((M * L : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) * A₀.toMatrix =
          A₀.toMatrix * ((M * L : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) ∧
        ∀ φ : EuclideanSpace ℂ (Qubits n),
          (∀ N ∈ S, act (N : Matrix (Qubits n) (Qubits n) ℂ) φ = φ) →
          act ((M * L : Matrix.unitaryGroup (Qubits n) ℂ) : Matrix (Qubits n) (Qubits n) ℂ) φ =
            act (L : Matrix (Qubits n) (Qubits n) ℂ) φ) := by sorry

end HeisenbergRep.Knill
