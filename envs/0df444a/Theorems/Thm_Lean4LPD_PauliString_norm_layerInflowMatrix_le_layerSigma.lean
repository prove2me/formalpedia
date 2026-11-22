-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_le_layerSigma
-- name    : Lean4LPD.PauliString.norm_layerInflowMatrix_le_layerSigma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:31:42.665216+00:00
-- url     : https://prove2.me/theorems/65626c76-4286-4a42-8485-130ed9ae5dee
-- title:
--   Pauli String: norm layer Inflow Matrix le layer Sigma
-- statement:
--   The layer-inflow bound with no hypothesis on the angles: `apd:eq:layer_inflow` with
--   `σ = max_l |sin θ_l|`. Neither positivity of the sines nor monotonicity of sine on an interval of
--   angles is required, which is more general than the paper's statement.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L832-L836
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L832-L836

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

theorem Lean4LPD.PauliString.norm_layerInflowMatrix_le_layerSigma (L : List (PauliString n × ℝ)) {kh : ℕ}
    (hL : IsLayer kh (L.map Prod.fst)) (w j : ℕ) :
    ‖layerInflowMatrix L w j‖
      ≤ ((w + j * (kh - 1)).choose j : ℝ) * layerSigma L ^ j := by sorry
