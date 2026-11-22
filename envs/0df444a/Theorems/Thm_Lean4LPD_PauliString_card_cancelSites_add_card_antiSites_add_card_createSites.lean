-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_card_cancelSites_add_card_antiSites_add_card_createSites
-- name    : Lean4LPD.PauliString.card_cancelSites_add_card_antiSites_add_card_createSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:58:55.603913+00:00
-- url     : https://prove2.me/theorems/f45e3c86-da90-4f31-819f-3da170dec55f
-- title:
--   Pauli String: card cancel Sites add card anti Sites add card create Sites
-- statement:
--   **The site count of `G`.** Every site `G` acts on either cancels a site of `s`, survives as a
--   locally anticommuting site, or is new.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L200-L204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L200-L204

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

theorem Lean4LPD.PauliString.card_cancelSites_add_card_antiSites_add_card_createSites (G s : PauliString n) :
    (cancelSites G s).card + (antiSites G s).card + (createSites G s).card = weight G := by sorry
