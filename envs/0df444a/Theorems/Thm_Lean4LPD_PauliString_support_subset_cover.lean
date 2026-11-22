-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_support_subset_cover
-- name    : Lean4LPD.PauliString.support_subset_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:56.275818+00:00
-- url     : https://prove2.me/theorems/ca642798-4fa2-42f3-83d0-02274dc50816
-- title:
--   Pauli String: support subset cover
-- statement:
--   **Containment.** Everything one layer can reach from `p` is supported in the light cone of
--   `supp p`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L319-L349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L319-L349

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.PauliString
variable {n kh : ℕ} {G H p q : PauliString n} {L : List (PauliString n)} {S T : Finset (Fin n)}

theorem Lean4LPD.PauliString.support_subset_cover : ∀ {L : List (PauliString n)},
    (L.Pairwise fun G H => Disjoint (support G) (support H)) →
    ∀ {p q : PauliString n}, q ∈ oneLayer L p → support q ⊆ cover L (support p) := by sorry
