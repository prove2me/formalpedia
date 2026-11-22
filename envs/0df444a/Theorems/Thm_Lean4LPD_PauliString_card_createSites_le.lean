-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_card_createSites_le
-- name    : Lean4LPD.PauliString.card_createSites_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:31.827247+00:00
-- url     : https://prove2.me/theorems/617e662b-d61b-41d6-a5d9-ee9f2c438ec8
-- title:
--   Pauli String: card create Sites le
-- statement:
--   At most `|G| - 1` new sites can be created by an anticommuting `G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L290-L294
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L290-L294

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

theorem Lean4LPD.PauliString.card_createSites_le (h : sympForm G s = 1) :
    (createSites G s).card ≤ weight G - 1 := by sorry
