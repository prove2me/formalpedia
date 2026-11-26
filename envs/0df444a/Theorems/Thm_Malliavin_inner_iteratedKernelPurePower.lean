-- Prove2me | Theorems.Thm_Malliavin_inner_iteratedKernelPurePower
-- name    : Malliavin.inner_iteratedKernelPurePower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:07:08.829013+00:00
-- url     : https://prove2.me/theorems/2bc6d22a-2e51-4e08-b3a7-9df5df2c212e
-- title:
--   Malliavin: inner iterated Kernel Pure Power
-- statement:
--   The inner product of two pure powers is the corresponding one-particle inner product raised
--   to the tensor order.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L86-L104
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L86-L104

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin

theorem Malliavin.inner_iteratedKernelPurePower (n : ℕ)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (iteratedKernelPurePower n f) (iteratedKernelPurePower n g) =
      inner ℝ f g ^ n := by sorry
