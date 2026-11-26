-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_brownianWickPowerLp_eq_power
-- name    : Malliavin.BrownianIteratedConstruction.span_range_brownianWickPowerLp_eq_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:01.612831+00:00
-- url     : https://prove2.me/theorems/43e94b2a-278d-561f-bbdb-bad0570e50d3
-- title:
--   Brownian Iterated Construction: span range brownian Wick Power Lp eq power
-- statement:
--   For a fixed Brownian step sum, generalized Hermite values and ordinary powers have the same
--   algebraic span.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L54-L59
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPolynomialHermite.lean#L54-L59

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

theorem Malliavin.BrownianIteratedConstruction.span_range_brownianWickPowerLp_eq_power (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) :
    Submodule.span ℝ (Set.range (brownianWickPowerLp hB v)) =
      Submodule.span ℝ (Set.range (brownianStepPowerLp hB v)) := by sorry
