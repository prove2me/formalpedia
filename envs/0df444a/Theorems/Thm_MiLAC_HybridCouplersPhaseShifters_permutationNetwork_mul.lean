-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_permutationNetwork_mul
-- name    : MiLAC.HybridCouplersPhaseShifters.permutationNetwork_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:22.960414+00:00
-- url     : https://prove2.me/theorems/587116d4-c71d-4e15-a8ba-5e706c0f1da5
-- title:
--   Hybrid Couplers Phase Shifters: permutation Network mul
-- statement:
--   Permutation matrices multiply anti-homomorphically: `P_τ P_σ = P_(σ * τ)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L72-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L72-L75

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.permutationNetwork_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permutationNetwork τ * permutationNetwork σ = permutationNetwork (σ * τ) := by sorry
