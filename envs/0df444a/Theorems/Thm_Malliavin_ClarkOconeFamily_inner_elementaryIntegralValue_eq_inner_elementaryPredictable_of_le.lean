-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
-- name    : Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:27.16997+00:00
-- url     : https://prove2.me/theorems/ff48c6e5-06fd-5bec-a78f-7fa15271c074
-- title:
--   Clark Ocone Family: inner elementary Integral Value eq inner elementary Predictable of le
-- statement:
--   The Itô cross-inner-product identity for two chronologically disjoint elementary terms.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L123-L130
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L123-L130

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

theorem Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_of_le
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) (Y : lpMeas ℝ ℝ (𝓕 c) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hcd Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 c d Y) := by sorry
