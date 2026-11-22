-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_restr_univ
-- name    : Lean4LPD.PauliString.restr_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:32.956184+00:00
-- url     : https://prove2.me/theorems/6dd2838d-7352-4484-87af-bed120cbc1bf
-- title:
--   Pauli String: restr univ
-- statement:
--   The Pauli String construction uses the restr univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L403-L406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L403-L406

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

theorem Lean4LPD.PauliString.restr_univ (y : EuclideanSpace ℂ (PauliIndex n)) : restr univ y = y := by sorry
