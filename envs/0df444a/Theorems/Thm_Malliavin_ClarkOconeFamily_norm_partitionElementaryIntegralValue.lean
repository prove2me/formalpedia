-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_norm_partitionElementaryIntegralValue
-- name    : Malliavin.ClarkOconeFamily.norm_partitionElementaryIntegralValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:59.152664+00:00
-- url     : https://prove2.me/theorems/61a63de5-ec88-462d-a7ba-2f27249c21ee
-- title:
--   Clark Ocone Family: norm partition Elementary Integral Value
-- statement:
--   The finite adapted-step Brownian integral is an isometry.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L272-L279
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L272-L279

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

theorem Malliavin.ClarkOconeFamily.norm_partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    ‖C.partitionElementaryIntegralValue Q Z‖ =
      ‖partitionElementaryPredictable Q Z‖ := by sorry
