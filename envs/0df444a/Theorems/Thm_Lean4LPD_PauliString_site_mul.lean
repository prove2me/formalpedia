-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_site_mul
-- name    : Lean4LPD.PauliString.site_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:20.578842+00:00
-- url     : https://prove2.me/theorems/02e5941f-d02f-405b-900d-bb884766c2fd
-- title:
--   Pauli String: site mul
-- statement:
--   The Pauli String construction uses the site mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L99-L100
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L99-L100

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

theorem Lean4LPD.PauliString.site_mul (s t : PauliString n) (i : Fin n) :
    site (s * t) i = site s i + site t i := by sorry

attribute [defeq] Lean4LPD.PauliString.site_mul
