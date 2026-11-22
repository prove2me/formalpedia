-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_restr_sq
-- name    : Lean4LPD.PauliString.norm_restr_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:19.642456+00:00
-- url     : https://prove2.me/theorems/fb33732e-e85e-4d43-86e5-f5587bf79dfd
-- title:
--   Pauli String: norm restr sq
-- statement:
--   The Pauli String construction uses the norm restr sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L386-L392
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L386-L392

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

theorem Lean4LPD.PauliString.norm_restr_sq (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr S y‖ ^ 2 = ∑ p ∈ S, ‖y.ofLp p‖ ^ 2 := by sorry
