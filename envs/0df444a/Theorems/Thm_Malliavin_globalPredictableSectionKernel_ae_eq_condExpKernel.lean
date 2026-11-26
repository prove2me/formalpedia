-- Prove2me | Theorems.Thm_Malliavin_globalPredictableSectionKernel_ae_eq_condExpKernel
-- name    : Malliavin.globalPredictableSectionKernel_ae_eq_condExpKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:03.186476+00:00
-- url     : https://prove2.me/theorems/2866731f-722d-54cf-902e-c15dc5be8a20
-- title:
--   Malliavin: global Predictable Section Kernel ae eq cond Exp Kernel
-- statement:
--   Guard-free form of the global identification: for almost every time and almost every
--   sample, the global predictable-section kernel is the fixed-time conditional kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L457-L466
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/KernelIdentification.lean#L457-L466

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

theorem Malliavin.globalPredictableSectionKernel_ae_eq_condExpKernel
    (hB : IsPreBrownianReal B P) (hm : ∀ s, StronglyMeasurable (B s))
    (hgen : IsWienerGenerated B) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      ∀ᵐ w ∂P,
        globalPredictableSectionKernel P (Filtration.natural B hm) (t, w)
          = condExpKernel P (Filtration.natural B hm t) w := by sorry
