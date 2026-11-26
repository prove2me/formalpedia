-- Prove2me | Theorems.Thm_Malliavin_isSetAlgebra_pastCylinderEvents
-- name    : Malliavin.isSetAlgebra_pastCylinderEvents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:39.351849+00:00
-- url     : https://prove2.me/theorems/5ea555b7-6715-465a-a838-67b015c3be87
-- title:
--   Malliavin: is Set Algebra past Cylinder Events
-- statement:
--   Finite-coordinate past events form an algebra of sets.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L62-L71
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PastCylinderDensity.lean#L62-L71

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
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.isSetAlgebra_pastCylinderEvents (B : ℝ≥0 → W → ℝ) (a : ℝ≥0) :
    IsSetAlgebra (pastCylinderEvents B a) := by sorry
