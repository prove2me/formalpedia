-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
-- name    : Lean4LPD.PauliString.weight_phaseMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:18.268498+00:00
-- url     : https://prove2.me/theorems/b0048abc-084a-4cb2-95a2-0ad99a920d0b
-- title:
--   Pauli String: weight phase Mul
-- statement:
--   The weight does not see the phase: it is a function of the bit vectors alone. The partner
--   Pauli in the proof of `apd:thm:local_flow_k_local` is `±i G s` rather than the bare product
--   `G s`, and this is why bounding `|G s|` bounds it too.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L128-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L128-L129

module
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n : ℕ} {G s t : PauliString n} {i : Fin n}

theorem Lean4LPD.PauliString.weight_phaseMul (k : ZMod 4) (s : PauliString n) :
    weight (phaseMul k s) = weight s := by sorry

attribute [defeq] Lean4LPD.PauliString.weight_phaseMul
