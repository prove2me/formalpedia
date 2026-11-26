-- Prove2me | Theorems.Thm_Malliavin_adaptedIndicator_pastCylinder_mem_closure
-- name    : Malliavin.adaptedIndicator_pastCylinder_mem_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:46.954509+00:00
-- url     : https://prove2.me/theorems/b029f665-bf21-444b-afed-2524f8618d6d
-- title:
--   Malliavin: adapted Indicator past Cylinder mem closure
-- statement:
--   The adapted indicator of one finite-coordinate past event is approximable by smooth bounded
--   past Brownian cylinders.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L117-L209
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L117-L209

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
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.adaptedIndicator_pastCylinder_mem_closure
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓕 = Filtration.natural B hsm) (a : ℝ≥0)
    {s : Set W} (hs : s ∈ pastCylinderEvents B a) :
    adaptedIndicator (P := P) 𝓕 a
        (measurableSet_pastCylinderEvents hsm hnat a hs) ∈
      (pastCylinderSpan hB coordinate coordinate_apply hsm hnat a).topologicalClosure := by sorry
