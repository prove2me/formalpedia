-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_butterfly_eq_block
-- name    : MiLAC.HybridCouplersPhaseShifters.butterfly_eq_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:41:03.225481+00:00
-- url     : https://prove2.me/theorems/090eb279-2e61-493e-854f-69b2f0814fd9
-- title:
--   Hybrid Couplers Phase Shifters: butterfly eq block
-- statement:
--   Each butterfly block is a block `D(0, -2π i / 2^(L+1), 0)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L604-L616
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L604-L616

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.butterfly_eq_block (L : ℕ) (i : Fin (2 ^ L)) :
    butterfly L i = block 0 (-2 * Real.pi * (i : ℕ) / 2 ^ (L + 1)) 0 := by sorry
