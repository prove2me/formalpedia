-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_card_antiLayer_le_weight
-- name    : Lean4LPD.PauliString.card_antiLayer_le_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:29:58.410651+00:00
-- url     : https://prove2.me/theorems/78c2ac9a-13b1-4bff-b2ce-ca7e61fcde66
-- title:
--   Pauli String: card anti Layer le weight
-- statement:
--   **Disjoint supports bound the number of anticommuting generators by the Pauli weight.**
--   This is the combinatorial statement `|𝒜(p)| ≤ |p|` in `apd:thm:layer_inflow`: every
--   anticommuting generator meets the support of `p`, and distinct generators of a layer meet it in
--   disjoint sets of sites.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L339-L362
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L339-L362

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

theorem Lean4LPD.PauliString.card_antiLayer_le_weight (L : List (PauliString n)) {kh : ℕ}
    (hL : IsLayer kh L) (p : PauliIndex n) : (antiLayer L p).card ≤ wt p := by sorry
