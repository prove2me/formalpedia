-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_weight_mul_add_card_cancelSites
-- name    : Lean4LPD.PauliString.weight_mul_add_card_cancelSites
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:00.596158+00:00
-- url     : https://prove2.me/theorems/5be59099-b64f-41ba-985b-68d46c13705d
-- title:
--   Pauli String: weight mul add card cancel Sites
-- statement:
--   **The weight bookkeeping.** Cancelled sites are exactly what `s` loses and created sites
--   exactly what it gains, so the weight moves by `#create - #cancel`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L208-L217
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Weight.lean#L208-L217

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

theorem Lean4LPD.PauliString.weight_mul_add_card_cancelSites (G s : PauliString n) :
    weight (G * s) + (cancelSites G s).card = weight s + (createSites G s).card := by sorry
