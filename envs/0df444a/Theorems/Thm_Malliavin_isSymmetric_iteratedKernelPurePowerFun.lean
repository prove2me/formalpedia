-- Prove2me | Theorems.Thm_Malliavin_isSymmetric_iteratedKernelPurePowerFun
-- name    : Malliavin.isSymmetric_iteratedKernelPurePowerFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:16.557798+00:00
-- url     : https://prove2.me/theorems/223c4a8a-fd38-457c-b27e-865f4f0851e7
-- title:
--   Malliavin: is Symmetric iterated Kernel Pure Power Fun
-- statement:
--   Pointwise pure powers are invariant under every permutation of their coordinates.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L62-L67
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedKernelPurePower.lean#L62-L67

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_Malliavin_IteratedKernelPurePower
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin

theorem Malliavin.isSymmetric_iteratedKernelPurePowerFun (n : ℕ)
    (f : ℝ≥0 → ℝ) :
    IsSymmetric n (iteratedKernelPurePowerFun n f) := by sorry
