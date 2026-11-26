-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_dense_orderedChainSpan_of_wickChainCompatible
-- name    : Malliavin.BrownianIteratedConstruction.dense_orderedChainSpan_of_wickChainCompatible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:48.643798+00:00
-- url     : https://prove2.me/theorems/81446f1d-9988-5960-b69e-1f2b76afc9f5
-- title:
--   Brownian Iterated Construction: dense ordered Chain Span of wick Chain Compatible
-- statement:
--   Ambient Brownian polynomial density and Wick-chain compatibility imply ordered-chain
--   density.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L201-L212
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L201-L212

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.BrownianIteratedConstruction.dense_orderedChainSpan_of_wickChainCompatible
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    (hwick : BrownianWickChainCompatible hB) :
    Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by sorry
