-- Prove2me | Theorems.Thm_Malliavin_predictableTrimEquiv_ae_eq
-- name    : Malliavin.predictableTrimEquiv_ae_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:36.70747+00:00
-- url     : https://prove2.me/theorems/2ec5e16e-048b-495b-83a3-27bbce5fbd91
-- title:
--   Malliavin: predictable Trim Equiv ae eq
-- statement:
--   The trimmed representative agrees almost everywhere with the ambient representative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L48-L52
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PredictableDensity.lean#L48-L52

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.predictableTrimEquiv_ae_eq
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (u : PredictableProcessL2 𝓕 P) :
    (predictableTrimEquiv 𝓕 u : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (u : ℝ≥0 × W → ℝ) := by sorry
