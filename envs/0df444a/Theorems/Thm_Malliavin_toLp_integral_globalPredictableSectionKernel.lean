-- Prove2me | Theorems.Thm_Malliavin_toLp_integral_globalPredictableSectionKernel
-- name    : Malliavin.toLp_integral_globalPredictableSectionKernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:55.752216+00:00
-- url     : https://prove2.me/theorems/67e341ff-f397-43aa-9462-43977a8cfa95
-- title:
--   Malliavin: to Lp integral global Predictable Section Kernel
-- statement:
--   **The kernel operator is the projection**, at the level of `L²` classes: the class of the
--   global-kernel integral of `U` is exactly `predictableProjection 𝓕 U`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L577-L584
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L577-L584

import Definitions.Def_Malliavin_PredictableKernel
import Definitions.Def_Malliavin_TimewiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_Malliavin_KernelIdentification
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.toLp_integral_globalPredictableSectionKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) (U : TimeProcessL2 P) :
    (memLp_integral_globalPredictableSectionKernel hB hm hgen U).toLp _
      = (predictableProjection (Filtration.natural B hm) U : TimeProcessL2 P) := by sorry
