-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralRange_isOrtho
-- name    : Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralRange_isOrtho
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:31.31877+00:00
-- url     : https://prove2.me/theorems/51348ab1-9794-51c0-8357-789ece4b75aa
-- title:
--   Brownian Iterated Construction: brownian Multiple Integral Range is Ortho
-- statement:
--   The unclosed Brownian multiple-integral ranges of distinct orders are orthogonal.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L102-L108
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L102-L108

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos
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

theorem Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralRange_isOrtho
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n) :
    brownianMultipleIntegralRange hB m ⟂ brownianMultipleIntegralRange hB n := by sorry
