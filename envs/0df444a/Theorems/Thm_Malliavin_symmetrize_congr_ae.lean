-- Prove2me | Theorems.Thm_Malliavin_symmetrize_congr_ae
-- name    : Malliavin.symmetrize_congr_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:44:49.474716+00:00
-- url     : https://prove2.me/theorems/ad27be1f-5181-4d0f-946e-64b81ced3d33
-- title:
--   Malliavin: symmetrize congr ae
-- statement:
--   Symmetrization respects a.e.-equality (so it descends to `Lp`).
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L243-L253
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L243-L253

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] (μ : Measure T) [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ}

theorem Malliavin.symmetrize_congr_ae {n : ℕ} {f g : (Fin n → T) → E}
    (h : f =ᵐ[Measure.pi fun _ : Fin n => μ] g) :
    symmetrize n f =ᵐ[Measure.pi fun _ : Fin n => μ] symmetrize n g := by sorry
