-- Prove2me | Theorems.Thm_Malliavin_integral_inner_symmetrizeL_eq_factorial_smul_setIntegral
-- name    : Malliavin.integral_inner_symmetrizeL_eq_factorial_smul_setIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:17.163809+00:00
-- url     : https://prove2.me/theorems/80512728-d09a-5d12-a2c2-31f46bd81598
-- title:
--   Malliavin: integral inner symmetrize L eq factorial smul set Integral
-- statement:
--   Tiling identity for the pointwise inner product of two `L²` symmetrizations.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L38-L79
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L38-L79

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.integral_inner_symmetrizeL_eq_factorial_smul_setIntegral (n : ℕ)
    (f g : IteratedKernel n) :
    (∫ t, inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f t)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g t)
        ∂iteratedKernelMeasure n) =
      n.factorial • ∫ t in simplex ℝ≥0 n, inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f t)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g t)
        ∂iteratedKernelMeasure n := by sorry
