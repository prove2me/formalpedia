-- Prove2me | Theorems.Thm_Malliavin_elementaryFinsuppToPredictable_single
-- name    : Malliavin.elementaryFinsuppToPredictable_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:40.700059+00:00
-- url     : https://prove2.me/theorems/f7d3e00a-9a96-42e2-97cf-dfdbc1699130
-- title:
--   Malliavin: elementary Finsupp To Predictable single
-- statement:
--   The predictable realization of a single formal generator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L248-L253
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L248-L253

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W]

theorem Malliavin.elementaryFinsuppToPredictable_single
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W)
    (x : ElementaryPredictableIndex 𝓕 P) (c : ℝ) :
    elementaryFinsuppToPredictable 𝓕 P (Finsupp.single x c) =
      c • elementaryPredictableGenerator 𝓕 P x := by sorry
