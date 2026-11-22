-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_site_one
-- name    : Lean4LPD.PauliString.site_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:17.511495+00:00
-- url     : https://prove2.me/theorems/48bd66a4-8236-41f1-8c1c-b247793a5809
-- title:
--   Pauli String: site one
-- statement:
--   The Pauli String construction uses the site one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L102-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L102-L102

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

theorem Lean4LPD.PauliString.site_one (i : Fin n) : site (1 : PauliString n) i = 0 := by sorry

attribute [defeq] Lean4LPD.PauliString.site_one
