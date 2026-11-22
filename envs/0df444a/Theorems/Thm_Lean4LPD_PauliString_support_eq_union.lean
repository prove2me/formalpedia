-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_support_eq_union
-- name    : Lean4LPD.PauliString.support_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:27.273737+00:00
-- url     : https://prove2.me/theorems/94b63503-8a5c-4dd5-bf86-a7969305a571
-- title:
--   Pauli String: support eq union
-- statement:
--   The three kinds of site exhaust `supp G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L174-L179
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L174-L179

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

theorem Lean4LPD.PauliString.support_eq_union (G s : PauliString n) :
    support G = cancelSites G s ∪ antiSites G s ∪ createSites G s := by sorry
