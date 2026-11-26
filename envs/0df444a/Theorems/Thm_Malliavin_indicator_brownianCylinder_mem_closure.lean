-- Prove2me | Theorems.Thm_Malliavin_indicator_brownianCylinder_mem_closure
-- name    : Malliavin.indicator_brownianCylinder_mem_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:58.989922+00:00
-- url     : https://prove2.me/theorems/a380dedc-faf7-539a-baa9-dc2887bba24d
-- title:
--   Malliavin: indicator brownian Cylinder mem closure
-- statement:
--   The indicator of one finite Brownian cylinder is approximable by Brownian polynomials.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L341-L414
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianCylinderDensity.lean#L341-L414

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.indicator_brownianCylinder_mem_closure
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    {s : Set W} (hs : s ∈ brownianCylinderEvents B) :
    indicatorConstLp 2 (measurableSet_brownianCylinderEvents hgen hs)
        (measure_ne_top P s) (1 : ℝ) ∈
      (brownianPolynomialSpan hB).topologicalClosure := by sorry
