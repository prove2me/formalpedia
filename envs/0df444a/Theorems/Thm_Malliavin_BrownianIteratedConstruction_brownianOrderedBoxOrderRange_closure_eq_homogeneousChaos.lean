-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos
-- name    : Malliavin.BrownianIteratedConstruction.brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:46.615228+00:00
-- url     : https://prove2.me/theorems/43dc31fc-9b4c-438d-a89e-9f8de0a7d012
-- title:
--   Brownian Iterated Construction: brownian Ordered Box Order Range closure eq homogeneous Chaos
-- statement:
--   At every positive order, finite ordered Brownian increment chains are dense in the
--   corresponding canonical homogeneous chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L131-L153
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L131-L153

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianOrderedBoxOrderRange hB (n + 1)).topologicalClosure =
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) := by sorry
