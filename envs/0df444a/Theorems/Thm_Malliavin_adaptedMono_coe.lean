-- Prove2me | Theorems.Thm_Malliavin_adaptedMono_coe
-- name    : Malliavin.adaptedMono_coe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:41:12.444981+00:00
-- url     : https://prove2.me/theorems/180ee42d-112e-56f2-aa91-543fa70cef9c
-- title:
--   Malliavin: adapted Mono coe
-- statement:
--   The promoted coefficient has the same ambient `L²` value.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L49-L53
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L49-L53

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

theorem Malliavin.adaptedMono_coe
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a c : ℝ≥0} (hac : a ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (adaptedMono 𝓕 hac Z : RandomL2 P) = (Z : RandomL2 P) := by sorry
