-- Prove2me | Theorems.Thm_Lean4LPD_PauliString_layerInflowMatrix_mulVec
-- name    : Lean4LPD.PauliString.layerInflowMatrix_mulVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:30:57.649438+00:00
-- url     : https://prove2.me/theorems/f008dd85-1095-4cd7-82ba-a4b318576bdf
-- title:
--   Pauli String: layer Inflow Matrix mul Vec
-- statement:
--   `layerInflowMatrix L w j` acts as `layerJump L j` restricted to low-weight inputs and
--   high-weight outputs. This connects the Schur bound to the Pauli coefficients of the conjugated
--   operator in `apd:thm:layer_inflow`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L857-L869
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerFlow.lean#L857-L869

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

theorem Lean4LPD.PauliString.layerInflowMatrix_mulVec (L : List (PauliString n × ℝ)) (w j : ℕ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    WithLp.toLp 2 (layerInflowMatrix L w j *ᵥ y.ofLp)
      = restr (highSet n w) (layerJump L j (restr (highSet n w)ᶜ y)) := by sorry
