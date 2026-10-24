-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_left_mul_matrix_derivation_identity
-- name    : OAI.PiExponent.FormalInterpolation.left_mul_matrix_derivation_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:07:13.076708+00:00
-- url     : https://prove2.me/theorems/43aa533f-37e8-4c1a-9ff2-f815c082fc28
-- title:
--   Derivation of a left multiplication matrix
-- statement:
--   For a finite basis of E over L, the matrix of left multiplication by D x equals the entrywise d-derivative of the matrix of left multiplication by x, plus the commutator with the matrix describing D on basis vectors. Expanding coordinates on each basis vector, applying both Leibniz rules, and using hcompat gives the identity. The statement retains finite dimensionality because its matrix identity uses finite matrices.

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Basis.Defs

theorem OAI.PiExponent.FormalInterpolation.left_mul_matrix_derivation_identity
    (k L E : Type) [Field k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E]
    [IsScalarTower k L E] [FiniteDimensional L E]
    (d : Derivation k L L) (D : Derivation k E E)
    (hcompat : ∀ a : L, D (algebraMap L E a) = algebraMap L E (d a))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι L E) (A : Matrix ι ι L)
    (hA : ∀ (i j : ι), A i j = b.repr (D (b j)) i) (x : E) :
    Matrix.map (Algebra.leftMulMatrix b x) d +
        A * Algebra.leftMulMatrix b x - Algebra.leftMulMatrix b x * A =
      Algebra.leftMulMatrix b (D x) := by sorry
