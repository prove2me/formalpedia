-- Prove2me | Theorems.Thm_Lean4LPD_card_bits
-- name    : Lean4LPD.card_bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:07:25.814132+00:00
-- url     : https://prove2.me/theorems/9cc40576-ef37-4354-a002-8910fa9dd9b7
-- title:
--   Lean4 LPD: card bits
-- statement:
--   There are `2^n` basis states, so `Matrix (Bits n) (Bits n) ℂ` is *a* `2^n × 2^n` matrix
--   algebra. `Rotation.lean`'s closing `example` names the same algebra as
--   `Matrix (Fin (2^n)) (Fin (2^n)) ℂ`, which is a different Lean type; the reindexing along
--   `Bits n ≃ Fin (2^n)` is supplied by `PauliString.bitsEquivFin` in `Pauli/Tensor.lean`, together
--   with the induced equivalence of matrix algebras `PauliString.bitsMatrixEquiv`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L210-L210
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Matrix.lean#L210-L210

module
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD

theorem Lean4LPD.card_bits (n : ℕ) : Fintype.card (Bits n) = 2 ^ n := by sorry
