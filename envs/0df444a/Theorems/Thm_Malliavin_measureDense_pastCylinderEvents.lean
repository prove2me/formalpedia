-- Prove2me | Theorems.Thm_Malliavin_measureDense_pastCylinderEvents
-- name    : Malliavin.measureDense_pastCylinderEvents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:04.088277+00:00
-- url     : https://prove2.me/theorems/6c28e3c1-1584-5c3d-855b-a6d44ece2ea6
-- title:
--   Malliavin: measure Dense past Cylinder Events
-- statement:
--   Finite-coordinate past events are measure-dense for the restriction of the probability
--   measure to the natural filtration at time `a`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L100-L112
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L100-L112

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.measureDense_pastCylinderEvents
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0) :
    @Measure.MeasureDense W (𝓕 a) (P.trim (𝓕.le a))
      (pastCylinderEvents B a) := by sorry
