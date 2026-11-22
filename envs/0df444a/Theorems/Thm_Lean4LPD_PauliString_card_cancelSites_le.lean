-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_card_cancelSites_le
-- name    : Lean4LPD.PauliString.card_cancelSites_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:30.21528+00:00
-- url     : https://prove2.me/theorems/94ef0d67-95d2-405b-ab33-e1571b396f47
-- title:
--   Pauli String: card cancel Sites le
-- statement:
--   At most `|G| - 1` sites of `s` can be cancelled by an anticommuting `G`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L283-L287
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L283-L287

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

theorem Lean4LPD.PauliString.card_cancelSites_le (h : sympForm G s = 1) :
    (cancelSites G s).card ≤ weight G - 1 := by sorry
