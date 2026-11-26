-- Prove2me | Theorems.Thm_Malliavin_norm_symmetrizeL_le
-- name    : Malliavin.norm_symmetrizeL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:47:24.463795+00:00
-- url     : https://prove2.me/theorems/99f950ef-9f07-4813-9d13-42355732b53d
-- title:
--   Malliavin: norm symmetrize L le
-- statement:
--   The operator norm of symmetrization is at most `1`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L315-L327
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/Symmetrization.lean#L315-L327

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

theorem Malliavin.norm_symmetrizeL_le (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ‖symmetrizeL E (μ := μ) n p‖ ≤ 1 := by sorry
