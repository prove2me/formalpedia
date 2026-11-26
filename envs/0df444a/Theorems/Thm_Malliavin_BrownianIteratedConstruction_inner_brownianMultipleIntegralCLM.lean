-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianMultipleIntegralCLM
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianMultipleIntegralCLM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:46.917556+00:00
-- url     : https://prove2.me/theorems/493a5b33-9cda-4dd2-8a6a-2a3880b8cb7e
-- title:
--   Brownian Iterated Construction: inner brownian Multiple Integral CLM
-- statement:
--   Polarized same-order isometry for the canonical Brownian multiple operators.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L61-L76
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L61-L76

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
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.inner_brownianMultipleIntegralCLM
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f g : IteratedKernel n) :
    inner ℝ (brownianMultipleIntegralCLM hB n f)
        (brownianMultipleIntegralCLM hB n g) =
      (n.factorial : ℝ) * inner ℝ
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f)
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 g) := by sorry
