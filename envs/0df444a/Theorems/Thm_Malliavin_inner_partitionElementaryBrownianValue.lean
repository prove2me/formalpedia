-- Prove2me | Theorems.Thm_Malliavin_inner_partitionElementaryBrownianValue
-- name    : Malliavin.inner_partitionElementaryBrownianValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:22:00.637067+00:00
-- url     : https://prove2.me/theorems/3086e4d2-5ceb-58e3-9670-e14369e99285
-- title:
--   Malliavin: inner partition Elementary Brownian Value
-- statement:
--   The construction-level Itô inner-product identity for adapted step processes on a common
--   partition.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L620-L659
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ElementaryIto.lean#L620-L659

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

theorem Malliavin.inner_partitionElementaryBrownianValue
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) {n : ℕ} (Q : Partition n)
    (Z Y : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    inner ℝ (partitionElementaryBrownianValue hB hsm hnat Q Z)
        (partitionElementaryBrownianValue hB hsm hnat Q Y) =
      inner ℝ (partitionElementaryPredictable Q Z)
        (partitionElementaryPredictable Q Y) := by sorry
