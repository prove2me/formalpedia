-- Prove2me | Theorems.Thm_Malliavin_isSetAlgebra_brownianCylinderEvents
-- name    : Malliavin.isSetAlgebra_brownianCylinderEvents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:52.886178+00:00
-- url     : https://prove2.me/theorems/be6e2ca5-dac3-5341-8a1a-084366c2c8d4
-- title:
--   Malliavin: is Set Algebra brownian Cylinder Events
-- statement:
--   The Malliavin construction uses the is Set Algebra brownian Cylinder Events property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L269-L277
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L269-L277

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
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.isSetAlgebra_brownianCylinderEvents (B : ℝ≥0 → W → ℝ) :
    IsSetAlgebra (brownianCylinderEvents B) := by sorry
