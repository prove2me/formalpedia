-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_permutationNetwork_mul_eq_submatrix
-- name    : MiLAC.HybridCouplersPhaseShifters.permutationNetwork_mul_eq_submatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:35.172316+00:00
-- url     : https://prove2.me/theorems/7818497d-91cd-47bb-8f7d-49cea1195b87
-- title:
--   Hybrid Couplers Phase Shifters: permutation Network mul eq submatrix
-- statement:
--   Left-multiplying by a permutation matrix permutes the rows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L78-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L78-L80

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.permutationNetwork_mul_eq_submatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) (M : Network n) :
    permutationNetwork σ * M = M.submatrix σ id := by sorry
