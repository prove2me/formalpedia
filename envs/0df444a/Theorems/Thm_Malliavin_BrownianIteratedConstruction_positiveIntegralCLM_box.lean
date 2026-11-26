-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_positiveIntegralCLM_box
-- name    : Malliavin.BrownianIteratedConstruction.positiveIntegralCLM_box
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:49:40.958481+00:00
-- url     : https://prove2.me/theorems/84f4517f-729f-4c1f-b839-6458b2cce8a9
-- title:
--   Brownian Iterated Construction: positive Integral CLM box
-- statement:
--   The positive-order full-kernel operator has the required Brownian ordered-box value.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L681-L686
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L681-L686

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_BrownianIterated
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
open Malliavin.BrownianIteratedConstruction
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.positiveIntegralCLM_box
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1)) (a : OrderedBoxIndex (n + 1)) :
    positiveIntegralCLM hB n (boxKernel a.u a.v) = chainIntegralLp hB a.u a.v := by sorry
