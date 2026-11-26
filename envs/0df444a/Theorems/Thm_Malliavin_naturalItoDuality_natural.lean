-- Prove2me | Theorems.Thm_Malliavin_naturalItoDuality_natural
-- name    : Malliavin.naturalItoDuality_natural
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:46:45.676045+00:00
-- url     : https://prove2.me/theorems/c249bc92-766d-426d-b2bc-db1e2b077032
-- title:
--   Malliavin: natural Ito Duality natural
-- statement:
--   Malliavin--Itô duality for every `D12` functional and natural predictable integrand.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L329-L345
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L329-L345

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.naturalItoDuality_natural
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm)
    (F : D12 P) (U : PredictableProcessL2 𝓕 P) :
    inner ℝ (F.1 - expectationL2 F.1) (naturalItoIntegral hB hsm hnat U) =
      inner ℝ
        (predictableProjection 𝓕
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F))) U := by sorry
