-- Prove2me | Theorems.Thm_FowlerLSQC_Canonical_so4_eq_magic_su2_tensor_su2
-- name    : FowlerLSQC.Canonical.so4_eq_magic_su2_tensor_su2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:35:34.181241+00:00
-- url     : https://prove2.me/theorems/2c9f47f0-1c93-4e17-9dbb-0af1dfb5a78a
-- title:
--   $SO(4)=Q^\dagger\,(SU(2)\otimes SU(2))\,Q$
-- statement:
--   Conjugation by the magic-basis matrix $Q$ of (4.3) identifies the local special unitary gates with the real rotations of $\mathbb R^4$:
--   $$
--   SO(4)=Q^\dagger\,\big(SU(2)\otimes SU(2)\big)\,Q .
--   $$
--   Precisely:
--   1. for all $A,B\in SU(2)$, the matrix $Q^\dagger(A\otimes B)Q$ is real, orthogonal and of determinant one;
--   2. every real orthogonal $4\times4$ matrix $O$ of determinant one equals $Q^\dagger(A\otimes B)Q$ for some $A,B\in SU(2)$.
--
--   This is the fact that turns the real orthogonal matrices $\tilde O_1,\tilde O_2$ of the construction into tensor products of single-qubit gates $G_{1A}\otimes G_{1B}$ and $G_{2A}\otimes G_{2B}$.
--
--   **Formalization Note** $SO(4)$ is `Matrix.specialOrthogonalGroup (Fin 4) ℝ`, cast entrywise into $\mathbb C$; $SU(2)$ is `Matrix.specialUnitaryGroup Bool ℂ`; qubit A is the first Kronecker factor.
--
--   Differences from the source:
--   - encoding: the set identity $SO(4)=Q^\dagger SU(2)\otimes SU(2)Q$ → the two inclusions, with $SO(4)$ as real matrices cast entrywise into $\mathbb C$; reason: equality of sets is the two inclusions.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §4.3, p.50 (PDF p.68), citing its Ref. [163]

import Mathlib
import Definitions.Def_FowlerLSQC_Canonical_magicQ

open scoped Kronecker Matrix

namespace FowlerLSQC.Canonical

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §4.3, p.50
(PDF p.68), quoting [163]: `SO(4) = Q† SU(2) ⊗ SU(2) Q`, where `Q` is the matrix of (4.3).

Both inclusions are stated: (1) for all `A, B ∈ SU(2)`, `Q†(A ⊗ B)Q` is a real special orthogonal
matrix; (2) every real special orthogonal `4 × 4` matrix `O` equals `Q†(A ⊗ B)Q` for some
`A, B ∈ SU(2)`.

**Formalization Note.** `SO(4)` is `Matrix.specialOrthogonalGroup (Fin 4) ℝ` (real orthogonal,
determinant 1), embedded in complex matrices entrywise by `Complex.ofReal`; the magic basis is
indexed by `Fin 4` (columns of `Q`). `SU(2)` is `Matrix.specialUnitaryGroup Bool ℂ`; qubit A is
the first Kronecker factor. -/
theorem so4_eq_magic_su2_tensor_su2 :
    (∀ A ∈ Matrix.specialUnitaryGroup Bool ℂ, ∀ B ∈ Matrix.specialUnitaryGroup Bool ℂ,
      ∃ O ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ,
        O.map (fun x : ℝ => (x : ℂ)) = magicQᴴ * (A ⊗ₖ B) * magicQ) ∧
    (∀ O ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ,
      ∃ A ∈ Matrix.specialUnitaryGroup Bool ℂ, ∃ B ∈ Matrix.specialUnitaryGroup Bool ℂ,
        O.map (fun x : ℝ => (x : ℂ)) = magicQᴴ * (A ⊗ₖ B) * magicQ) := by sorry

end FowlerLSQC.Canonical
