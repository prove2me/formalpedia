-- Prove2me | Theorems.Thm_Malliavin_ae_pos_finiteHorizonTimeMeasure
-- name    : Malliavin.ae_pos_finiteHorizonTimeMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:23:07.702578+00:00
-- url     : https://prove2.me/theorems/a8a9f91c-3b0a-5d60-a588-59174a84ab53
-- title:
--   Malliavin: ae pos finite Horizon Time Measure
-- statement:
--   Almost every time in a finite horizon is strictly positive; the omitted endpoint `0` is a
--   Lebesgue-null singleton.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L46-L51
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableKernel.lean#L46-L51

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

theorem Malliavin.ae_pos_finiteHorizonTimeMeasure (T : ℝ≥0) :
    ∀ᵐ t ∂finiteHorizonTimeMeasure T, 0 < t := by sorry
