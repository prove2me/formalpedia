-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_apply
-- name    : Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:52.396788+00:00
-- url     : https://prove2.me/theorems/d1da5a3c-5e6a-5937-8638-92fc073b0308
-- title:
--   Brownian Iterated Construction: brownian Multiple Integral CLM apply
-- statement:
--   The Brownian Iterated Construction construction uses the brownian Multiple Integral CLM apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L41-L46
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L41-L46

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

theorem Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_apply
    (hB : IsPreBrownianReal B P) (n : ℕ) (f : IteratedKernel n) :
    brownianMultipleIntegralCLM hB n f =
      (n.factorial : ℝ) • integralCLM hB n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) := by sorry
