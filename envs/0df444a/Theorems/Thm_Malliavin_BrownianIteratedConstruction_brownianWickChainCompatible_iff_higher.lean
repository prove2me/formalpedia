-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickChainCompatible_iff_higher
-- name    : Malliavin.BrownianIteratedConstruction.brownianWickChainCompatible_iff_higher
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:36.753567+00:00
-- url     : https://prove2.me/theorems/003c5836-66c4-4590-87bf-dcdeab092481
-- title:
--   Brownian Iterated Construction: brownian Wick Chain Compatible iff higher
-- statement:
--   Orders zero and one are automatic, so Wick-chain compatibility is exactly its higher-order
--   part.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L144-L168
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L144-L168

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

theorem Malliavin.BrownianIteratedConstruction.brownianWickChainCompatible_iff_higher (hB : IsPreBrownianReal B P) :
    BrownianWickChainCompatible hB ↔ BrownianHigherWickChainCompatible hB := by sorry
