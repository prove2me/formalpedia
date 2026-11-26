-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom
-- name    : Malliavin.BrownianIteratedConstruction.canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:19.684696+00:00
-- url     : https://prove2.me/theorems/4a76dd0b-7d18-43e0-8413-7d7fb80b3143
-- title:
--   Brownian Iterated Construction: canonical Ordered Box Multiple Integral Map eq ordered Box To Random
-- statement:
--   On finite ordered-box combinations, the bundled canonical multiple-integral map is exactly
--   the Brownian increment-chain map.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L115-L120
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L115-L120

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]

theorem Malliavin.BrownianIteratedConstruction.canonicalOrderedBoxMultipleIntegralMap_eq_orderedBoxToRandom
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    canonicalOrderedBoxMultipleIntegralMap hB n = orderedBoxToRandom hB n := by sorry
