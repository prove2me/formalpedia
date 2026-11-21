-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_parallel_blockDiagonal_one
-- name    : MiLAC.HybridCouplersPhaseShifters.isLayered_parallel_blockDiagonal_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:51.270752+00:00
-- url     : https://prove2.me/theorems/50b78f16-add0-410b-9a0e-11cf731fd12e
-- title:
--   Hybrid Couplers Phase Shifters: is Layered parallel block Diagonal one
-- statement:
--   Placing an identity below the block diagonal matrix of a layer gives a network admitting a
--   `layered` decomposition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L484-L496
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L484-L496

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.isLayered_parallel_blockDiagonal_one {n : ℕ} (layer : Layer n) (m : ℕ) :
    IsLayered (parallel (Matrix.reindex (finCongr layer.size) (finCongr layer.size)
      (blockDiagonal layer.θ₁₁ layer.θ₁₂ layer.θ₂₁ layer.φ)) (1 : Network m)) := by sorry
