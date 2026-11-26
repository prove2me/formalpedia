-- Prove2me | Theorems.Thm_Malliavin_norm_iteratedKernelPurePower
-- name    : Malliavin.norm_iteratedKernelPurePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:24:45.085746+00:00
-- url     : https://prove2.me/theorems/1310f6c3-5713-5e26-8e3b-3b65b8eec3a4
-- title:
--   Malliavin: norm iterated Kernel Pure Power
-- statement:
--   Norm formula for a pure-power kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L114-L122
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L114-L122

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin

theorem Malliavin.norm_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖iteratedKernelPurePower n f‖ = ‖f‖ ^ n := by sorry
