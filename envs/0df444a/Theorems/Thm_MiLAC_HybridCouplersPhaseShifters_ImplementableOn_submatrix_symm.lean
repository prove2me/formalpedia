-- Prove2me | Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_submatrix_symm
-- name    : MiLAC.HybridCouplersPhaseShifters.ImplementableOn.submatrix_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T22:40:42.968772+00:00
-- url     : https://prove2.me/theorems/c9756e40-0256-433d-ad3c-cbb1005ee4c2
-- title:
--   Implementable On: submatrix symm
-- statement:
--   Relabelling the rows and the columns of an implementable matrix into `Fin n` independently
--   gives an implementable network.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L299-L308
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MicrowaveNetworks/HybridCouplersPhaseShifters.lean#L299-L308

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters

theorem MiLAC.HybridCouplersPhaseShifters.ImplementableOn.submatrix_symm {ι : Type*}
    {M : Matrix ι ι ℂ} (h : ImplementableOn M) {n : ℕ} (e₁ e₂ : ι ≃ Fin n) :
    Implementable (M.submatrix e₁.symm e₂.symm) := by sorry
