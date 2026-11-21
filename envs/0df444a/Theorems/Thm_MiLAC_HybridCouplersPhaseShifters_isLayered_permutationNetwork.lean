-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_permutationNetwork
-- name    : MiLAC.HybridCouplersPhaseShifters.isLayered_permutationNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:32.126405+00:00
-- url     : https://prove2.me/theorems/e102d01f-fd5c-417a-8a96-74d205934e58
-- title:
--   Hybrid Couplers Phase Shifters: is Layered permutation Network
-- statement:
--   A permutation network admits a `layered` decomposition, with no layers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L419-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L419-L421

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.isLayered_permutationNetwork {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsLayered (permutationNetwork σ) := by sorry
