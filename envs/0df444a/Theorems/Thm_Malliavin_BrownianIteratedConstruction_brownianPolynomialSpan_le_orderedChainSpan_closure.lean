-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPolynomialSpan_le_orderedChainSpan_closure
-- name    : Malliavin.BrownianIteratedConstruction.brownianPolynomialSpan_le_orderedChainSpan_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:52.652534+00:00
-- url     : https://prove2.me/theorems/59ade260-d779-4946-8518-8d22397dcb66
-- title:
--   Brownian Iterated Construction: brownian Polynomial Span le ordered Chain Span closure
-- statement:
--   Under Wick-chain compatibility, the entire Brownian polynomial span lies in the ordered-chain
--   closure.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L190-L196
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L190-L196

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

theorem Malliavin.BrownianIteratedConstruction.brownianPolynomialSpan_le_orderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hwick : BrownianWickChainCompatible hB) :
    brownianPolynomialSpan hB ≤
      (brownianOrderedChainSpan hB).topologicalClosure := by sorry
