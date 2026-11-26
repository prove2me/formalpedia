-- Prove2me | Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
-- name    : Malliavin.centeredNaturalItoIntegralIsometry_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:40:01.651894+00:00
-- url     : https://prove2.me/theorems/eafb68ff-d21a-5c93-a809-53742babf80b
-- title:
--   Malliavin: centered Natural Ito Integral Isometry apply
-- statement:
--   The centered isometry has the same ambient value as `naturalItoIntegral`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L490-L496
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ItoConstruction.lean#L490-L496

import Definitions.Def_Malliavin_ElementaryIto
import Definitions.Def_Malliavin_PredictableDensity
import Definitions.Def_Malliavin_ItoConstruction
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

theorem Malliavin.centeredNaturalItoIntegralIsometry_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (U : PredictableProcessL2 𝓕 P) :
    (centeredNaturalItoIntegralIsometry hB hsm hnat U : RandomL2 P) =
      naturalItoIntegral hB hsm hnat U := by sorry

attribute [defeq] Malliavin.centeredNaturalItoIntegralIsometry_apply
