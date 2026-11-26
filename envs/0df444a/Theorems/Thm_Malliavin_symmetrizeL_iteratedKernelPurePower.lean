-- Prove2me | Theorems.Thm_Malliavin_symmetrizeL_iteratedKernelPurePower
-- name    : Malliavin.symmetrizeL_iteratedKernelPurePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:32.777349+00:00
-- url     : https://prove2.me/theorems/87f210e5-b5d8-5de9-839e-183d5682cbd2
-- title:
--   Malliavin: symmetrize L iterated Kernel Pure Power
-- statement:
--   Pure-power kernels are fixed by the `L²` symmetrization operator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L70-L82
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L70-L82

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin

theorem Malliavin.symmetrizeL_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
        (iteratedKernelPurePower n f) =
      iteratedKernelPurePower n f := by sorry
