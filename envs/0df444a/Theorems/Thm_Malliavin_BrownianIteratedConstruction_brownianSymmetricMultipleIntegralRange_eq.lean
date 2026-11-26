-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSymmetricMultipleIntegralRange_eq
-- name    : Malliavin.BrownianIteratedConstruction.brownianSymmetricMultipleIntegralRange_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:44.965801+00:00
-- url     : https://prove2.me/theorems/40987b5f-e82f-4d92-8c80-adb1809c1e3e
-- title:
--   Brownian Iterated Construction: brownian Symmetric Multiple Integral Range eq
-- statement:
--   Symmetrization does not change the orderwise canonical Brownian range.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L123-L155
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L123-L155

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Definitions.Def_Malliavin_BrownianMultipleIntegral
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.brownianSymmetricMultipleIntegralRange_eq
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    brownianSymmetricMultipleIntegralRange hB n =
      brownianMultipleIntegralRange hB n := by sorry
