-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_to_equiv
-- name    : MiLAC.HybridCouplersPhaseShifters.ImplementableOn.to_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:20.461392+00:00
-- url     : https://prove2.me/theorems/c8b438d9-c462-4e41-984b-1ee38627781e
-- title:
--   Implementable On: to equiv
-- statement:
--   An implementable matrix is implementable after any finite port relabelling.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L196-L207
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L196-L207

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.ImplementableOn.to_equiv {ι : Type*} {M : Matrix ι ι ℂ}
    (h : ImplementableOn M) (n : ℕ) (e : ι ≃ Fin n) :
    Implementable (Matrix.reindex e e M) := by sorry
