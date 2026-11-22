-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_highNorm_restr_le
-- name    : Lean4LPD.PauliString.highNorm_restr_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:28:46.035023+00:00
-- url     : https://prove2.me/theorems/aef51cc4-4443-4fa3-8e00-76f9e38e163b
-- title:
--   Pauli String: high Norm restr le
-- statement:
--   Truncation only decreases the high-weight norms: restricting a coefficient vector to any set
--   of classes cannot increase its mass above any threshold.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Flow.lean#L527-L536
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Flow.lean#L527-L536

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
open Lean4LPD.PauliString
variable {n : ℕ} {G : PauliString n} {p : PauliIndex n} {kh w w' : ℕ}

theorem Lean4LPD.PauliString.highNorm_restr_le (S : Finset (PauliIndex n)) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖restr (highSet n w) (restr S y)‖ ≤ ‖restr (highSet n w) y‖ := by sorry
