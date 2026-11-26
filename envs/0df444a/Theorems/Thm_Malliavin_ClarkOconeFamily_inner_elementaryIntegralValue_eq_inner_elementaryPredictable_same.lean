-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
-- name    : Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:32.988806+00:00
-- url     : https://prove2.me/theorems/60508877-3e45-5b68-9413-706745532c31
-- title:
--   Clark Ocone Family: inner elementary Integral Value eq inner elementary Predictable same
-- statement:
--   The Itô cross-inner-product identity for two elementary terms on the same interval.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L133-L200
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L133-L200

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

theorem Malliavin.ClarkOconeFamily.inner_elementaryIntegralValue_eq_inner_elementaryPredictable_same
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b)
    (Z Y : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    inner ℝ (C.elementaryIntegralValue hab Z) (C.elementaryIntegralValue hab Y) =
      inner ℝ (elementaryPredictable 𝓕 a b Z) (elementaryPredictable 𝓕 a b Y) := by sorry
