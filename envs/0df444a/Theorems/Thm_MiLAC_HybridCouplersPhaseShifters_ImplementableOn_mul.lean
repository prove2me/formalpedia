-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_mul
-- name    : MiLAC.HybridCouplersPhaseShifters.ImplementableOn.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:09.561634+00:00
-- url     : https://prove2.me/theorems/f6c1c1a6-ef7a-435b-8e37-91db37d44234
-- title:
--   Implementable On: mul
-- statement:
--   The product of two implementable matrices is implementable.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L229-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L229-L236

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.ImplementableOn.mul {ι : Type*} [Fintype ι] {A B : Matrix ι ι ℂ}
    (hA : ImplementableOn A) (hB : ImplementableOn B) : ImplementableOn (A * B) := by sorry
