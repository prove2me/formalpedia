-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_parallel_mul
-- name    : MiLAC.HybridCouplersPhaseShifters.parallel_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:25.101063+00:00
-- url     : https://prove2.me/theorems/52d7f794-1400-4ece-ad0e-bf8db7f11d03
-- title:
--   Hybrid Couplers Phase Shifters: parallel mul
-- statement:
--   The product of two parallels is the parallel of the products.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L88-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L88-L90

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.parallel_mul {n m : ℕ} (A B : Network n) (C D : Network m) :
    parallel A C * parallel B D = parallel (A * B) (C * D) := by sorry
