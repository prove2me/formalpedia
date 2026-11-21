-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_mul
-- name    : MiLAC.HybridCouplersPhaseShifters.IsLayered.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:11.173174+00:00
-- url     : https://prove2.me/theorems/eb64801e-29bb-4365-9cad-0822df46b2e2
-- title:
--   Is Layered: mul
-- statement:
--   The product of two networks admitting a `layered` decomposition admits one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L448-L450
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L448-L450

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.IsLayered.mul {n : ℕ} {A B : Network n} (hA : IsLayered A) (hB : IsLayered B) :
    IsLayered (A * B) := by sorry
