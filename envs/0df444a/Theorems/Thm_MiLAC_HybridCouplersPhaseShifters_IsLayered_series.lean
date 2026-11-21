-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_series
-- name    : MiLAC.HybridCouplersPhaseShifters.IsLayered.series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:30.961925+00:00
-- url     : https://prove2.me/theorems/29a8c310-437c-466e-b339-2c9611705815
-- title:
--   Is Layered: series
-- statement:
--   The series of two networks admitting a `layered` decomposition admits one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L435-L445
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L435-L445

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.IsLayered.series {n : ℕ} {A B : Network n} (hA : IsLayered A) (hB : IsLayered B) :
    IsLayered (series A B) := by sorry
