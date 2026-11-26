-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianStepPowerLp_mem_orderedChainSpan_closure
-- name    : Malliavin.BrownianIteratedConstruction.brownianStepPowerLp_mem_orderedChainSpan_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:17.425128+00:00
-- url     : https://prove2.me/theorems/d974bf1e-356c-5ca7-97fb-6fecfeeb2579
-- title:
--   Brownian Iterated Construction: brownian Step Power Lp mem ordered Chain Span closure
-- statement:
--   Wick-chain compatibility puts every Brownian step-sum power in the ordered-chain closure.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L173-L184
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L173-L184

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

theorem Malliavin.BrownianIteratedConstruction.brownianStepPowerLp_mem_orderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hwick : BrownianWickChainCompatible hB)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianStepPowerLp hB v n ∈
      (brownianOrderedChainSpan hB).topologicalClosure := by sorry
