-- Prove2me | Theorems.Thm_Malliavin_inner_sub_centeredNaturalItoRangeProjection
-- name    : Malliavin.inner_sub_centeredNaturalItoRangeProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:54:01.575429+00:00
-- url     : https://prove2.me/theorems/74c68829-9cf3-43b2-8be3-336e1ec1f5ad
-- title:
--   Malliavin: inner sub centered Natural Ito Range Projection
-- statement:
--   Equivalently, the residual is orthogonal to the integral of every predictable process.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L284-L295
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L284-L295

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
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

theorem Malliavin.inner_sub_centeredNaturalItoRangeProjection
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker)
    (U : PredictableProcessL2 𝓅 P) :
    inner ℝ (G - (centeredNaturalItoRangeProjection hB hsm hnat G :
        (CameronMartin.expectationMap P).ker))
      (centeredNaturalItoIntegralIsometry hB hsm hnat U) = 0 := by sorry
