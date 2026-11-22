-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_restr_apply
-- name    : Lean4LPD.PauliString.restr_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:15:40.259441+00:00
-- url     : https://prove2.me/theorems/0b1ebc45-c44a-453f-bfdc-5284299a5b32
-- title:
--   Pauli String: restr apply
-- statement:
--   The Pauli String construction uses the restr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L383-L384
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Coeff.lean#L383-L384

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

theorem Lean4LPD.PauliString.restr_apply (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n))
    (p : PauliIndex n) : (restr S y).ofLp p = if p ∈ S then y.ofLp p else 0 := by sorry

attribute [defeq] Lean4LPD.PauliString.restr_apply
