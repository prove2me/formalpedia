-- Prove2me | Theorems.Thm_Malliavin_norm_partitionElementaryBrownianValue
-- name    : Malliavin.norm_partitionElementaryBrownianValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:31:23.936962+00:00
-- url     : https://prove2.me/theorems/72cc784b-4e44-5752-aff0-e9c3a4029855
-- title:
--   Malliavin: norm partition Elementary Brownian Value
-- statement:
--   Construction-level Itô isometry for common-partition adapted `L²` step processes.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L663-L672
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L663-L672

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.norm_partitionElementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    ‖partitionElementaryBrownianValue hB hsm hnat Q Z‖ =
      ‖partitionElementaryPredictable Q Z‖ := by sorry
