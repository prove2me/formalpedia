-- Prove2me | Theorems.Thm_Malliavin_pastCylinderDense
-- name    : Malliavin.pastCylinderDense
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:35.593844+00:00
-- url     : https://prove2.me/theorems/839fec8e-874d-5099-a2ed-03003be09c56
-- title:
--   Malliavin: past Cylinder Dense
-- statement:
--   Smooth bounded functions of finitely many Brownian coordinates are dense in every time
--   section of the natural filtration.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L216-L297
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L216-L297

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
set_option maxHeartbeats 250000
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.pastCylinderDense
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) :
    PastCylinderDense hB coordinate coordinate_apply hsm hnat := by sorry
