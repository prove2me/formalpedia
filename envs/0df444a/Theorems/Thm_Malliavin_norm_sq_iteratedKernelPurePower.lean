-- Prove2me | Theorems.Thm_Malliavin_norm_sq_iteratedKernelPurePower
-- name    : Malliavin.norm_sq_iteratedKernelPurePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:14:48.673132+00:00
-- url     : https://prove2.me/theorems/3e2727c3-4094-53be-a5f6-d8ae1ffd038f
-- title:
--   Malliavin: norm sq iterated Kernel Pure Power
-- statement:
--   Squared norm formula for a pure-power kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L107-L111
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L107-L111

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin

theorem Malliavin.norm_sq_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖iteratedKernelPurePower n f‖ ^ 2 = (‖f‖ ^ 2) ^ n := by sorry
