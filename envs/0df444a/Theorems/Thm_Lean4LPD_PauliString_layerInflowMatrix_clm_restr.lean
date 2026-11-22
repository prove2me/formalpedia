-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerInflowMatrix_clm_restr
-- name    : Lean4LPD.PauliString.layerInflowMatrix_clm_restr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:29.992613+00:00
-- url     : https://prove2.me/theorems/d8e46ed5-a7ab-4ad4-8e71-14eefdaed657
-- title:
--   Pauli String: layer Inflow Matrix clm restr
-- statement:
--   A `j`-jump inflow into weights above `w` only uses the input's coefficients of weight above
--   `w'`, for any `w'` with `w' + j (k_h - 1) ≤ w`. This localizes the inflow on the lower rung, as
--   needed by `apd:rmk:multijump`; it follows from the coefficient support bound in
--   `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L943-L965
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L943-L965

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

theorem Lean4LPD.PauliString.layerInflowMatrix_clm_restr (L : List (PauliString n × ℝ)) {kh w w' j : ℕ}
    (hk : ∀ g ∈ L, weight g.1 ≤ kh) (hw : w' + j * (kh - 1) ≤ w)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    Lean4LPD.clm (layerInflowMatrix L w j) y
      = Lean4LPD.clm (layerInflowMatrix L w j) (restr (highSet n w') y) := by sorry
