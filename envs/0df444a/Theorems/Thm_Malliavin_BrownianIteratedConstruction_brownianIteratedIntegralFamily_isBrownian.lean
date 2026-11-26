-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianIteratedIntegralFamily_isBrownian
-- name    : Malliavin.BrownianIteratedConstruction.brownianIteratedIntegralFamily_isBrownian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:53:49.207415+00:00
-- url     : https://prove2.me/theorems/5c04888f-84d5-5680-ada5-b94ea5d280dc
-- title:
--   Brownian Iterated Construction: brownian Iterated Integral Family is Brownian
-- statement:
--   The canonical completed family agrees with Brownian increment products on every ordered
--   box.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianOrderedBoxDensity.lean#L478-L485
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianOrderedBoxDensity.lean#L478-L485

import Definitions.Def_Malliavin_BrownianIterated
import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.brownianIteratedIntegralFamily_isBrownian
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W]
    {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    (brownianIteratedIntegralFamily hB hsm).IsBrownian B := by sorry
