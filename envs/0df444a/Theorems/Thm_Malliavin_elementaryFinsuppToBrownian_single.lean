-- Prove2me | Theorems.Thm_Malliavin_elementaryFinsuppToBrownian_single
-- name    : Malliavin.elementaryFinsuppToBrownian_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:15.655307+00:00
-- url     : https://prove2.me/theorems/f095ce39-293c-5edb-a83c-f71f9e06bc54
-- title:
--   Malliavin: elementary Finsupp To Brownian single
-- statement:
--   The Brownian realization of a single formal generator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L258-L265
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L258-L265

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
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.elementaryFinsuppToBrownian_single
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (x : ElementaryPredictableIndex 𝓕 P) (c : ℝ) :
    elementaryFinsuppToBrownian hB hsm hnat (Finsupp.single x c) =
      c • elementaryBrownianGenerator hB hsm hnat x := by sorry
