-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_IsLayer_disjoint_of_mem
-- name    : Lean4LPD.PauliString.IsLayer.disjoint_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:34.505463+00:00
-- url     : https://prove2.me/theorems/1c066dc0-dbf2-49f8-b05a-063a3559f53b
-- title:
--   Is Layer: disjoint of mem
-- statement:
--   Disjointness in the pointwise form the count needs. Stated separately because `List.Pairwise`
--   orders its pairs and `Disjoint` does not care.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L252-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L252-L254

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.IsLayer.disjoint_of_mem (hL : IsLayer kh L) (hG : G ∈ L) (hH : H ∈ L) (hne : G ≠ H) :
    Disjoint (support G) (support H) := by sorry
