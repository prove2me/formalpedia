-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_stepToRandom_mem_orderedChainSpan
-- name    : Malliavin.BrownianIteratedConstruction.stepToRandom_mem_orderedChainSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:12.895006+00:00
-- url     : https://prove2.me/theorems/104250f0-28b2-5089-a143-dd080ac6d016
-- title:
--   Brownian Iterated Construction: step To Random mem ordered Chain Span
-- statement:
--   Every finite Brownian step sum belongs already to the algebraic ordered-chain span.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L117-L128
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L117-L128

import Definitions.Def_Malliavin_BrownianHermite
import Definitions.Def_Malliavin_BrownianCylinderDensity
import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianPolynomialHermite
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.stepToRandom_mem_orderedChainSpan (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    stepToRandom hB v ∈ brownianOrderedChainSpan hB := by sorry
