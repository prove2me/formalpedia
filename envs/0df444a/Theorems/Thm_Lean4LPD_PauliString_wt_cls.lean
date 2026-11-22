-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_wt_cls
-- name    : Lean4LPD.PauliString.wt_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:28.840042+00:00
-- url     : https://prove2.me/theorems/eb1423f0-9c25-4604-aa5e-77d9e45f60b1
-- title:
--   Pauli String: wt cls
-- statement:
--   The Pauli String construction uses the wt cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L171-L171
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L171-L171

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

theorem Lean4LPD.PauliString.wt_cls (s : PauliString n) : wt (cls s) = weight s := by sorry
