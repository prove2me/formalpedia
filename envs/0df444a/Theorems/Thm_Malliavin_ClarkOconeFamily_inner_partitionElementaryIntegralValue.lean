-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_inner_partitionElementaryIntegralValue
-- name    : Malliavin.ClarkOconeFamily.inner_partitionElementaryIntegralValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:21:39.442868+00:00
-- url     : https://prove2.me/theorems/9c2d3e76-b663-5403-8125-ee4692715307
-- title:
--   Clark Ocone Family: inner partition Elementary Integral Value
-- statement:
--   The Itô inner-product identity for two adapted elementary step processes on a
--   common partition.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L221-L259
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L221-L259

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

theorem Malliavin.ClarkOconeFamily.inner_partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z Y : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    inner ℝ (C.partitionElementaryIntegralValue Q Z)
        (C.partitionElementaryIntegralValue Q Y) =
      inner ℝ (partitionElementaryPredictable Q Z)
        (partitionElementaryPredictable Q Y) := by sorry
