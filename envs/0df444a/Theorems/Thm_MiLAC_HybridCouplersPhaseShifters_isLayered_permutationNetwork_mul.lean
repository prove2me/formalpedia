-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_isLayered_permutationNetwork_mul
-- name    : MiLAC.HybridCouplersPhaseShifters.isLayered_permutationNetwork_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:54.25319+00:00
-- url     : https://prove2.me/theorems/efeb6d57-89fe-4767-809e-7f25e3ca046d
-- title:
--   Hybrid Couplers Phase Shifters: is Layered permutation Network mul
-- statement:
--   Left-multiplying a `layered` decomposition by a permutation matrix only changes its
--   outermost permutation: `σ₀` (if there are no layers) or the permutation of the topmost layer
--   (if there are).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L426-L432
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L426-L432

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.isLayered_permutationNetwork_mul {n : ℕ} (τ σ₀ : Equiv.Perm (Fin n))
    (layers : List (Layer n)) : IsLayered (permutationNetwork τ * layered σ₀ layers) := by sorry
