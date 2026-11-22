-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_herm_eq_or_eq_neg
-- name    : Lean4LPD.PauliString.herm_eq_or_eq_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:21:17.27794+00:00
-- url     : https://prove2.me/theorems/e2a888c2-2a96-4f94-aaa7-1601882bd36c
-- title:
--   Pauli String: herm eq or eq neg
-- statement:
--   Any self-adjoint representative of a class is `± herm`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L151-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L151-L157

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

theorem Lean4LPD.PauliString.herm_eq_or_eq_neg {s : PauliString n} (hs : IsSelfAdjoint s) :
    s = herm (cls s) ∨ s = phaseMul 2 (herm (cls s)) := by sorry
