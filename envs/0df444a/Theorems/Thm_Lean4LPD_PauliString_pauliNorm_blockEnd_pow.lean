-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_pauliNorm_blockEnd_pow
-- name    : Lean4LPD.PauliString.pauliNorm_blockEnd_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:44:23.41874+00:00
-- url     : https://prove2.me/theorems/6ccda1b1-7387-4802-8d54-80be979fcc63
-- title:
--   Pauli String: pauli Norm block End pow
-- statement:
--   Evolution through whole blocks preserves the Pauli 2-norm, the invariance needed for the
--   norm-level part of `apd:thm:triangle`. This is where Hermiticity of the generators is used.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L204-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/TruncationError.lean#L204-L209

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TrotterTruncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_TruncationError
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
open Finset
variable {n : ℕ}

theorem Lean4LPD.PauliString.pauliNorm_blockEnd_pow {Gs : ℕ → PauliString n}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ) (period : ℕ)
    (O : Matrix (Bits n) (Bits n) ℂ) (r : ℕ) :
    pauliNorm (((blockEnd Gs θ period) ^ r) O) = pauliNorm O := by sorry
