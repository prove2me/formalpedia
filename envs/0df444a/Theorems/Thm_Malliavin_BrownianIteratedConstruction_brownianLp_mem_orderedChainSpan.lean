-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianLp_mem_orderedChainSpan
-- name    : Malliavin.BrownianIteratedConstruction.brownianLp_mem_orderedChainSpan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:18:10.496847+00:00
-- url     : https://prove2.me/theorems/1f58969f-8d2b-4d0e-abc9-c49b40bbc2a6
-- title:
--   Brownian Iterated Construction: brownian Lp mem ordered Chain Span
-- statement:
--   Every Brownian coordinate belongs already to the algebraic ordered-chain span.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L93-L112
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L93-L112

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

theorem Malliavin.BrownianIteratedConstruction.brownianLp_mem_orderedChainSpan (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    brownianLp hB t ∈ brownianOrderedChainSpan hB := by sorry
