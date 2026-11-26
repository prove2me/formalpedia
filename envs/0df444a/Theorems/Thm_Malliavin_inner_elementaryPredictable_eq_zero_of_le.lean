-- Prove2me | Theorems.Thm_Malliavin_inner_elementaryPredictable_eq_zero_of_le
-- name    : Malliavin.inner_elementaryPredictable_eq_zero_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:18.1155+00:00
-- url     : https://prove2.me/theorems/87f5ddde-d0f0-5e49-b988-2f2d9a7eb7a1
-- title:
--   Malliavin: inner elementary Predictable eq zero of le
-- statement:
--   Chronologically disjoint elementary predictable terms are orthogonal in product `L²`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L88-L120
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L88-L120

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
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

theorem Malliavin.inner_elementaryPredictable_eq_zero_of_le
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) {a b c d : ℝ≥0} (hbc : b ≤ c)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) = 0 := by sorry
