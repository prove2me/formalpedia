-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_congr
-- name    : Lean4LPD.PauliString.weight_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:44.702816+00:00
-- url     : https://prove2.me/theorems/ef081774-b64c-495c-963a-130a12cf3de8
-- title:
--   Pauli String: weight congr
-- statement:
--   The weight sees only the `(x, z)` data.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L162-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L162-L165

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

theorem Lean4LPD.PauliString.weight_congr {s t : PauliString n} (hx : s.x = t.x) (hz : s.z = t.z) :
    weight s = weight t := by sorry
