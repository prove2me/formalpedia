-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_toMatrix_mul
-- name    : Lean4LPD.PauliString.trace_toMatrix_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:53.652341+00:00
-- url     : https://prove2.me/theorems/9bc96f2b-b7b9-47d0-b8c2-b299f3a793d0
-- title:
--   Pauli String: trace to Matrix mul
-- statement:
--   **`Tr(s O)` is a character transform of a shifted diagonal of `O`.** The matrix `toMatrix s`
--   is monomial, so the double sum of the trace collapses to a single one: the `X`-part `s.x` selects
--   which off-diagonal of `O` is read, and the `Z`-part `s.z` supplies the character.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L222-L240
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L222-L240

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ}

theorem Lean4LPD.PauliString.trace_toMatrix_mul (s : PauliString n) (O : Matrix (Bits n) (Bits n) ℂ) :
    (toMatrix s * O).trace
      = iPow s.phase * ∑ b : Bits n, negOnePow (s.z ⬝ᵥ b) * O b (b + s.x) := by sorry
