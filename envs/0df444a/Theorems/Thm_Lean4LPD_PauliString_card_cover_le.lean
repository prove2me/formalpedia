-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_card_cover_le
-- name    : Lean4LPD.PauliString.card_cover_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:50.073772+00:00
-- url     : https://prove2.me/theorems/f6b26b20-485f-4a38-83b0-8e648d78f733
-- title:
--   Pauli String: card cover le
-- statement:
--   **The count.** A layer of `k_h`-local generators with disjoint supports has a light cone at
--   most `k_h` times as large as the set it starts from.
--
--   The factor is `k_h` and not `k_h + 1` because each firing generator *pays* for itself out of `S`:
--   its support meets `S`, the supports are disjoint, so the firing generators inject into `S ∩ U`,
--   and the part of `S` no generator touches is carried along unchanged.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L357-L395
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L357-L395

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.card_cover_le (hL : IsLayer kh L) (hkh : 1 ≤ kh) (S : Finset (Fin n)) :
    (cover L S).card ≤ kh * S.card := by sorry
