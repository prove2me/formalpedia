-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_mul_permutationNetwork_eq_submatrix
-- name    : MiLAC.HybridCouplersPhaseShifters.mul_permutationNetwork_eq_submatrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:14.45364+00:00
-- url     : https://prove2.me/theorems/6f63b878-2357-4c10-9af4-1f6975350257
-- title:
--   Hybrid Couplers Phase Shifters: mul permutation Network eq submatrix
-- statement:
--   Right-multiplying by a permutation matrix permutes the columns.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L83-L85
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L83-L85

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.mul_permutationNetwork_eq_submatrix {n : ℕ} (M : Network n) (σ : Equiv.Perm (Fin n)) :
    M * permutationNetwork σ = M.submatrix id σ.symm := by sorry
