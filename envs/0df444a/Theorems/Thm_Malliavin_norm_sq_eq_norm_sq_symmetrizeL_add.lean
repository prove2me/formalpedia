-- Prove2me | Theorems.Thm_Malliavin_norm_sq_eq_norm_sq_symmetrizeL_add
-- name    : Malliavin.norm_sq_eq_norm_sq_symmetrizeL_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:56:12.776945+00:00
-- url     : https://prove2.me/theorems/f09effcd-2969-5bf5-86b7-5c054c300e24
-- title:
--   Malliavin: norm sq eq norm sq symmetrize L add
-- statement:
--   Orthogonal decomposition: `‖f‖² = ‖f̃‖² + ‖f - f̃‖²` on `L²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L435-L441
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L435-L441

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_Symmetrization
set_option autoImplicit false
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open Malliavin
variable {T : Type*} {E : Type*}
variable [MeasurableSpace T] {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem Malliavin.norm_sq_eq_norm_sq_symmetrizeL_add (n : ℕ)
    (f : Lp E 2 (Measure.pi fun _ : Fin n => μ)) :
    ‖f‖ ^ 2 = ‖symmetrizeL E (μ := μ) n 2 f‖ ^ 2 + ‖f - symmetrizeL E (μ := μ) n 2 f‖ ^ 2 := by sorry
