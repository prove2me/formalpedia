-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_orderedBoxToIteratedKernel
-- name    : Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_orderedBoxToIteratedKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:19.550807+00:00
-- url     : https://prove2.me/theorems/4f623fd7-a38d-42fa-920a-c1a5f52d9f00
-- title:
--   Brownian Iterated Construction: brownian Multiple Integral CLM ordered Box To Iterated Kernel
-- statement:
--   The canonical multiple-integral operator maps a finite ordered-box combination to the matching
--   finite combination of Brownian increment chains.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L95-L102
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L95-L102

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

theorem Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_orderedBoxToIteratedKernel
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (c : OrderedBoxIndex n →₀ ℝ) :
    brownianMultipleIntegralCLM hB n (orderedBoxToIteratedKernel n c) =
      orderedBoxToRandom hB n c := by sorry
