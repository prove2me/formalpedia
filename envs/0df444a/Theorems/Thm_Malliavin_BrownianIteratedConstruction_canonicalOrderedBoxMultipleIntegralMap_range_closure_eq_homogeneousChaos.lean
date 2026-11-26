-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_canonicalOrderedBoxMultipleIntegralMap_range_closure_eq_homogeneousChaos
-- name    : Malliavin.BrownianIteratedConstruction.canonicalOrderedBoxMultipleIntegralMap_range_closure_eq_homogeneousChaos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:33:22.876672+00:00
-- url     : https://prove2.me/theorems/36d0ebc6-4423-4ba9-a0cc-d369ccad3b2f
-- title:
--   Brownian Iterated Construction: canonical Ordered Box Multiple Integral Map range closure eq homogeneous Chaos
-- statement:
--   The positive-order canonical multiple-integral map restricted to finite ordered boxes already
--   has dense range in the full canonical homogeneous chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L158-L164
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L158-L164

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

theorem Malliavin.BrownianIteratedConstruction.canonicalOrderedBoxMultipleIntegralMap_range_closure_eq_homogeneousChaos
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (LinearMap.range
        (canonicalOrderedBoxMultipleIntegralMap hB (n + 1))).topologicalClosure =
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) := by sorry
