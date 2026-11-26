-- Prove2me | Theorems.Thm_Malliavin_sub_centeredNaturalItoRangeProjection_mem_orthogonal
-- name    : Malliavin.sub_centeredNaturalItoRangeProjection_mem_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:14.122086+00:00
-- url     : https://prove2.me/theorems/2dc5e892-b4b0-444b-9925-845afa00146f
-- title:
--   Malliavin: sub centered Natural Ito Range Projection mem orthogonal
-- statement:
--   The residual after projecting a centered terminal variable is orthogonal to the entire
--   natural Itô range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L270-L280
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalItoRange.lean#L270-L280

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

theorem Malliavin.sub_centeredNaturalItoRangeProjection_mem_orthogonal
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    G - (centeredNaturalItoRangeProjection hB hsm hnat G :
      (CameronMartin.expectationMap P).ker) ∈
        (centeredNaturalItoRange hB hsm hnat)ᗮ := by sorry
