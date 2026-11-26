-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianMultipleIntegralCLM_of_ne
-- name    : Malliavin.BrownianIteratedConstruction.inner_brownianMultipleIntegralCLM_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:13:53.845355+00:00
-- url     : https://prove2.me/theorems/5f100e45-32cf-4478-91f8-ab2a67de9f8f
-- title:
--   Brownian Iterated Construction: inner brownian Multiple Integral CLM of ne
-- statement:
--   Canonical Brownian multiple integrals of different orders are orthogonal.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L80-L87
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L80-L87

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

theorem Malliavin.BrownianIteratedConstruction.inner_brownianMultipleIntegralCLM_of_ne
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (brownianMultipleIntegralCLM hB m f)
      (brownianMultipleIntegralCLM hB n g) = 0 := by sorry
