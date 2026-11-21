-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_of_netEquiv
-- name    : MiLAC.HybridCouplersPhaseShifters.IsLayered.of_netEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:33.558211+00:00
-- url     : https://prove2.me/theorems/1432288a-ef62-4c43-bfb0-b0da39d9220f
-- title:
--   Is Layered: of net Equiv
-- statement:
--   Admitting a `layered` decomposition is invariant under a relabelling of the ports.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L453-L467
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L453-L467

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.IsLayered.of_netEquiv {X Y : Σ n : ℕ, Network n}
    (h : NetEquiv X Y) (hY : IsLayered Y.2) : IsLayered X.2 := by sorry
