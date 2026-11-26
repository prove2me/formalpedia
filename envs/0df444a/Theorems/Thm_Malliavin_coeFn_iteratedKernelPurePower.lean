-- Prove2me | Theorems.Thm_Malliavin_coeFn_iteratedKernelPurePower
-- name    : Malliavin.coeFn_iteratedKernelPurePower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:34.464495+00:00
-- url     : https://prove2.me/theorems/387f659a-8929-533e-97c2-72632aa2ef85
-- title:
--   Malliavin: coe Fn iterated Kernel Pure Power
-- statement:
--   The canonical representative of a pure-power kernel is its pointwise coordinate product.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L55-L59
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L55-L59

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin

theorem Malliavin.coeFn_iteratedKernelPurePower (n : ℕ)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (iteratedKernelPurePower n f : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
      iteratedKernelPurePowerFun n f := by sorry
