-- Prove2me | Theorems.Thm_Malliavin_inner_multipleIntegralCLM_ne
-- name    : Malliavin.inner_multipleIntegralCLM_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:54:28.617484+00:00
-- url     : https://prove2.me/theorems/91293ec5-abca-522d-9bb0-f7f5b4a6a135
-- title:
--   Malliavin: inner multiple Integral CLM ne
-- statement:
--   Outputs of selected multiple operators of different orders are orthogonal.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L174-L178
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MultipleIntegral.lean#L174-L178

import Definitions.Def_Malliavin_IteratedIntegral
import Definitions.Def_Malliavin_MultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.inner_multipleIntegralCLM_ne (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (multipleIntegralCLM hB m f) (multipleIntegralCLM hB n g) = 0 := by sorry
