-- Prove2me | Theorems.Thm_Malliavin_finiteHorizonProductMeasure_eq_restrict
-- name    : Malliavin.finiteHorizonProductMeasure_eq_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:41.211442+00:00
-- url     : https://prove2.me/theorems/00dd181e-380a-5387-bf74-f46b3ad5ac89
-- title:
--   Malliavin: finite Horizon Product Measure eq restrict
-- statement:
--   Restricting the time measure before taking the product is the same as restricting the product
--   measure to `Set.Iic T ×ˢ Set.univ`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L66-L71
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L66-L71

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.finiteHorizonProductMeasure_eq_restrict (T : ℝ≥0) :
    finiteHorizonProductMeasure P T =
      (nonnegativeLebesgueMeasure.prod P).restrict (Set.Iic T ×ˢ Set.univ) := by sorry
