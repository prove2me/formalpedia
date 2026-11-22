-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_sympForm_herm_partner_of_commute
-- name    : Lean4LPD.PauliString.sympForm_herm_partner_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:38.082876+00:00
-- url     : https://prove2.me/theorems/be87e916-7c3d-4ac6-a6cf-ef90afd74dd2
-- title:
--   Pauli String: symp Form herm partner of commute
-- statement:
--   Commuting with a generator makes its partner translation preserve the symplectic test
--   against another generator. Supporting lemma for the fixed `𝒜(p)` in
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L377-L381
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L377-L381

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Schur
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.PauliString
open Finset Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

theorem Lean4LPD.PauliString.sympForm_herm_partner_of_commute (G H : PauliString n)
    (hGH : sympForm G H = 0) (p : PauliIndex n) :
    sympForm G (herm (partner H p)) = sympForm G (herm p) := by sorry
