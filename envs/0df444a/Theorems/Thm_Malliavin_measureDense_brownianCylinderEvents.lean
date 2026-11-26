-- Prove2me | Theorems.Thm_Malliavin_measureDense_brownianCylinderEvents
-- name    : Malliavin.measureDense_brownianCylinderEvents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:23.018488+00:00
-- url     : https://prove2.me/theorems/7bb80bf2-1f88-4aeb-88ae-04680735ad53
-- title:
--   Malliavin: measure Dense brownian Cylinder Events
-- statement:
--   Brownian cylinders are measure-dense in a Brownian-generated probability space.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L302-L308
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L302-L308

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_Malliavin_BrownianCylinderDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.measureDense_brownianCylinderEvents
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    P.MeasureDense (brownianCylinderEvents B) := by sorry
