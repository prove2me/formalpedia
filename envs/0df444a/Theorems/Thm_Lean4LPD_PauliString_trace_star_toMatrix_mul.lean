-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_trace_star_toMatrix_mul
-- name    : Lean4LPD.PauliString.trace_star_toMatrix_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:14:48.605799+00:00
-- url     : https://prove2.me/theorems/c47b1410-d7de-4019-8c6d-24fc517830e5
-- title:
--   Pauli String: trace star to Matrix mul
-- statement:
--   **The trace pairing of two Pauli operators.** Zero unless the two strings carry the same
--   `X`- and `Z`-parts; `2^n` times a fourth root of unity when they do.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L176-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Trace.lean#L176-L191

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

theorem Lean4LPD.PauliString.trace_star_toMatrix_mul (s t : PauliString n) :
    (star (toMatrix s) * toMatrix t).trace
      = if s.x = t.x ∧ s.z = t.z then (2 : ℂ) ^ n * iPow (star s * t).phase else 0 := by sorry
