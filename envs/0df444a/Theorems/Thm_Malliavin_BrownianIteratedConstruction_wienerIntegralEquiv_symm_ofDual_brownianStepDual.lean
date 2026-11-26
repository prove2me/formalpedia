-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_wienerIntegralEquiv_symm_ofDual_brownianStepDual
-- name    : Malliavin.BrownianIteratedConstruction.wienerIntegralEquiv_symm_ofDual_brownianStepDual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:22:25.623131+00:00
-- url     : https://prove2.me/theorems/14273835-d127-40a1-b995-66e83333a37c
-- title:
--   Brownian Iterated Construction: wiener Integral Equiv symm of Dual brownian Step Dual
-- statement:
--   Under the first-chaos equivalence, the Cameron--Martin generator of a formal step sum is
--   sent back to its deterministic step kernel.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L54-L76
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianPurePowerDuality.lean#L54-L76

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
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

theorem Malliavin.BrownianIteratedConstruction.wienerIntegralEquiv_symm_ofDual_brownianStepDual
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (v : ℝ≥0 →₀ ℝ) :
    (wienerIntegralEquiv hB).symm
        (LinearIsometryEquiv.ofEq _ _
          (space_eq_firstChaos hB coordinate coordinate_apply generated)
          (CameronMartin.ofDual P (brownianStepDual coordinate v))) =
      stepToLp v := by sorry
