-- Prove2me | Theorems.Thm_LindbladShallow_lemma_2_2
-- name    : LindbladShallow.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:25.226535+00:00
-- url     : https://prove2.me/theorems/0b538ef7-1142-4e14-900f-0d05487c90ef
-- title:
--   Lemma 2.2 — channel transfer and composition
-- statement:
--   Let $U_C,U_D$ be unitaries on a system $S$ and an auxiliary register $A$, and $E_C\psi=U_C(\psi\otimes|0\rangle_A)$, $E_D\psi=U_D(\psi\otimes|0\rangle_A)$.
--
--   1. The induced channel is
--   $$\Phi_C(Z)=\mathrm{Tr}_A(E_CZE_C^\dagger)=\sum_aK_aZK_a^\dagger,\qquad K_a=(I_S\otimes\langle a|_A)E_C,\qquad \sum_aK_a^\dagger K_a=I.$$
--   2. With the same environment space, $\|\Phi_C-\Phi_D\|_\diamond\le2\|E_C-E_D\|$.
--   3. For any two channels $\Phi,\Psi$ on a common space and every integer $m\ge1$, $\|\Phi^m-\Psi^m\|_\diamond\le m\|\Phi-\Psi\|_\diamond$.
--
--   This converts initialized operator-norm (column) errors into diamond-norm channel errors and composes them over segments; it is used throughout the proof of Theorem 2.1.
--
--   Differences from the source:
--   - generalization: a unitary circuit U_C → any unitary matrix on S ⊗ A; reason: the statement uses only the circuit's unitary; a circuit's unitary is a unitary, so this specializes to the source
--   - encoding: channel (CPTP map) → QAlgorithms.IsChannel: a finite normalized Kraus family; reason: in finite dimension these are exactly the CPTP maps
--   - encoding: ‖Φ‖_⋄ = sup_{r≥1} sup_{Z≠0} ‖(Φ⊗I_r)(Z)‖₁/‖Z‖₁ → dnorm: an ℝ≥0∞ supremum over every r ≥ 1 and every nonzero complex Z, reference factor first (id_r ⊗ Φ), trace norm QAlgorithms.traceNorm; reason: Lean convention; reordering tensor factors changes no value and the ℝ≥0∞ supremum has no junk value
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 2.2, p.11, Eqs. (3)–(5)

import Mathlib
import Definitions.Def_LindbladShallow_dnorm

open scoped Matrix ComplexOrder ENNReal

namespace LindbladShallow

open QAlgorithms

/-- **Lemma 2.2** (Channel transfer and composition; arXiv:2610.05362, held version
sha256 8f4637ef…, p.11). Let `U_C`, `U_D` be unitaries on system `S` ⊗ auxiliary register `A`,
`E_Cψ := U_C(ψ ⊗ |0⟩_A)`, `E_Dψ := U_D(ψ ⊗ |0⟩_A)`.
(3) The induced channel is `Φ_C(Z) = Tr_A(E_C Z E_C†) = Σ_a K_a Z K_a†` with
`K_a := (I_S ⊗ ⟨a|_A)E_C` and `Σ_a K_a†K_a = I`;
(4) `‖Φ_C − Φ_D‖_⋄ ≤ 2‖E_C − E_D‖` (same environment space);
(5) for any two channels `Φ, Ψ` on a common space and every integer `m ≥ 1`,
`‖Φ^m − Ψ^m‖_⋄ ≤ m‖Φ − Ψ‖_⋄`.

**Formalization Note** "Unitary circuit" is read as any unitary on `S ⊗ A` (a circuit's unitary
is one). Channels are `QAlgorithms.IsChannel` (finite normalized Kraus families = CPTP maps in
finite dimension). `|0⟩_A` is a fixed basis vector `a₀`. -/
theorem lemma_2_2 {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (a₀ : A) (UC UD : Matrix (S × A) (S × A) ℂ)
    (hUC : UC ∈ Matrix.unitaryGroup (S × A) ℂ) (hUD : UD ∈ Matrix.unitaryGroup (S × A) ℂ) :
    let EC : Matrix (S × A) S ℂ := UC * vacIso a₀
    let ED : Matrix (S × A) S ℂ := UD * vacIso a₀
    let K : A → Matrix S S ℂ := fun a => Matrix.of fun i j => EC (i, a) j
    (∀ Z : Matrix S S ℂ, isoChannel EC Z = ∑ a : A, K a * Z * Matrix.conjTranspose (K a)) ∧
      (∑ a : A, Matrix.conjTranspose (K a) * K a = 1) ∧
      dnorm (isoChannel EC - isoChannel ED) ≤ ENNReal.ofReal (2 * opNorm (EC - ED)) ∧
      (∀ Φ Ψ : Superop S S, IsChannel Φ → IsChannel Ψ → ∀ m : ℕ, 1 ≤ m →
        dnorm (Φ^[m] - Ψ^[m]) ≤ (m : ℝ≥0∞) * dnorm (Φ - Ψ)) := by sorry

end LindbladShallow
