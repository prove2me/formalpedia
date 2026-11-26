-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_exists_brownianMultipleIntegralCLM_eq_simplexIntegral
-- name    : Malliavin.BrownianIteratedConstruction.exists_brownianMultipleIntegralCLM_eq_simplexIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:37.209123+00:00
-- url     : https://prove2.me/theorems/8cfca1ce-d979-468b-b34b-a31aff1bf363
-- title:
--   Brownian Iterated Construction: exists brownian Multiple Integral CLM eq simplex Integral
-- statement:
--   Every simplex-kernel value of positive order is represented by a canonical symmetric
--   multiple integral.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L93-L113
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegral.lean#L93-L113

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

theorem Malliavin.BrownianIteratedConstruction.exists_brownianMultipleIntegralCLM_eq_simplexIntegral
    (hB : IsPreBrownianReal B P) (n : ℕ)
    (g : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    ∃ f : IteratedKernel (n + 1),
      brownianMultipleIntegralCLM hB (n + 1) f =
        simplexIntegral hB (n + 1) g := by sorry
