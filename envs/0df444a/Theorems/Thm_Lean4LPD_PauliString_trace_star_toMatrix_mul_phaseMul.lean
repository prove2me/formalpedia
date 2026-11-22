-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_star_toMatrix_mul_phaseMul
-- name    : Lean4LPD.PauliString.trace_star_toMatrix_mul_phaseMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:06.605822+00:00
-- url     : https://prove2.me/theorems/ffccf76b-efbb-4821-aaec-c0dd73b1e9a1
-- title:
--   Pauli String: trace star to Matrix mul phase Mul
-- statement:
--   **Phase variants are not orthogonal**, and this records why the orthogonal family is the `4^n`
--   signless classes rather than the `4·4^n` group elements: `i·s` pairs with `s` to give `2^n · i`,
--   not `0`. Anything that wants an orthonormal basis must normalize the phase first.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L210-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L210-L219

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Trace
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {s t u : PauliString n}

theorem Lean4LPD.PauliString.trace_star_toMatrix_mul_phaseMul (k : ZMod 4) (s : PauliString n) :
    (star (toMatrix s) * toMatrix (phaseMul k s)).trace = (2 : ℂ) ^ n * iPow k := by sorry
