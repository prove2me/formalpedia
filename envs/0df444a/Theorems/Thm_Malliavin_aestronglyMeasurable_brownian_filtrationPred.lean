-- Prove2me | Theorems.Thm_Malliavin_aestronglyMeasurable_brownian_filtrationPred
-- name    : Malliavin.aestronglyMeasurable_brownian_filtrationPred
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:28:11.54471+00:00
-- url     : https://prove2.me/theorems/a2f470c1-75b7-5795-b839-456c66edca14
-- title:
--   Malliavin: aestrongly Measurable brownian filtration Pred
-- statement:
--   The endpoint coordinate `B t` has a strict-past-measurable version for every `t > 0`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L62-L85
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalFiltrationLeftContinuous.lean#L62-L85

import Definitions.Def_Malliavin_PointwiseCondExp
import Definitions.Def_Malliavin_NaturalFiltrationLeftContinuous
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.aestronglyMeasurable_brownian_filtrationPred
    {B : ℝ≥0 → W → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) (ht : 0 < t) :
    AEStronglyMeasurable[filtrationPred (Filtration.natural B hm) t] (B t) P := by sorry
