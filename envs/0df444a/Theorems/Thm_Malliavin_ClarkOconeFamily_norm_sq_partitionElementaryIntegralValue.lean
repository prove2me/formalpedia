-- Prove2me | Theorems.Thm_Malliavin_ClarkOconeFamily_norm_sq_partitionElementaryIntegralValue
-- name    : Malliavin.ClarkOconeFamily.norm_sq_partitionElementaryIntegralValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:21:49.972351+00:00
-- url     : https://prove2.me/theorems/542efa2e-1573-4fcf-88b6-c8675f769456
-- title:
--   Clark Ocone Family: norm sq partition Elementary Integral Value
-- statement:
--   The finite adapted-step Brownian integral preserves squared norms.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L262-L269
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L262-L269

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

theorem Malliavin.ClarkOconeFamily.norm_sq_partitionElementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    ‖C.partitionElementaryIntegralValue Q Z‖ ^ 2 =
      ‖partitionElementaryPredictable Q Z‖ ^ 2 := by sorry
