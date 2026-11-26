-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_orderedBox
-- name    : Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_orderedBox
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:23.622142+00:00
-- url     : https://prove2.me/theorems/e6a1c814-71ca-4b1a-b02e-6e4195885cca
-- title:
--   Brownian Iterated Construction: brownian Multiple Integral CLM ordered Box
-- statement:
--   The canonical symmetrized Brownian multiple-integral operator has the Brownian chain value
--   on every ordered box.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBox.lean#L84-L119
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBox.lean#L84-L119

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_orderedBox
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (a : OrderedBoxIndex n) :
    brownianMultipleIntegralCLM hB n (boxKernel a.u a.v) =
      chainIntegralLp hB a.u a.v := by sorry
