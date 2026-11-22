-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_restr_add_restr_compl
-- name    : Lean4LPD.PauliString.restr_add_restr_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:46.44509+00:00
-- url     : https://prove2.me/theorems/783063a1-0201-4a53-b86b-a9407191ae45
-- title:
--   Pauli String: restr add restr compl
-- statement:
--   `x = x_R + x_B`: a coefficient vector is the sum of its restrictions to a set of classes and
--   to the complement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L417-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L417-L421

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

theorem Lean4LPD.PauliString.restr_add_restr_compl (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    restr S y + restr Sᶜ y = y := by sorry
