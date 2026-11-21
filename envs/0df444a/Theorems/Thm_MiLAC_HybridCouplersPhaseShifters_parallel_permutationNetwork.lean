-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_permutationNetwork
-- name    : MiLAC.HybridCouplersPhaseShifters.parallel_permutationNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:29.116902+00:00
-- url     : https://prove2.me/theorems/e9311da7-4c67-4a0c-84d6-a6589fcb0bc7
-- title:
--   Hybrid Couplers Phase Shifters: parallel permutation Network
-- statement:
--   The parallel of two permutation networks is a permutation network.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L93-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L93-L99

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.parallel_permutationNetwork {n m : ℕ}
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    parallel (permutationNetwork σ) (permutationNetwork τ) =
      permutationNetwork (finSumFinEquiv.permCongr (Equiv.sumCongr σ τ)) := by sorry
