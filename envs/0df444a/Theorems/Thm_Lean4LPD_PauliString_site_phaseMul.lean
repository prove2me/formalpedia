-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
-- name    : Lean4LPD.PauliString.site_phaseMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:20.118197+00:00
-- url     : https://prove2.me/theorems/d32cd7f6-e0a0-4328-a974-5a8741bb1fe2
-- title:
--   Pauli String: site phase Mul
-- statement:
--   The Pauli String construction uses the site phase Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L104-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L104-L105

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

theorem Lean4LPD.PauliString.site_phaseMul (k : ZMod 4) (s : PauliString n) (i : Fin n) :
    site (phaseMul k s) i = site s i := by sorry

attribute [defeq] Lean4LPD.PauliString.site_phaseMul
