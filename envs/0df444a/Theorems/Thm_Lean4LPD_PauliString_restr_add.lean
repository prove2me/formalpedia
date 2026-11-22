-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_restr_add
-- name    : Lean4LPD.PauliString.restr_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:36.806615+00:00
-- url     : https://prove2.me/theorems/b2072d13-10af-41f7-aef0-b55cb6860645
-- title:
--   Pauli String: restr add
-- statement:
--   The Pauli String construction uses the restr add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L408-L413
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L408-L413

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

theorem Lean4LPD.PauliString.restr_add (S : Finset (PauliIndex n)) (y z : EuclideanSpace ℂ (PauliIndex n)) :
    restr S (y + z) = restr S y + restr S z := by sorry
