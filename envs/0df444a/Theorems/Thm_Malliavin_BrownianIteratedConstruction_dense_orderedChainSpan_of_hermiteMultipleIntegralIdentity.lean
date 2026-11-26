-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_dense_orderedChainSpan_of_hermiteMultipleIntegralIdentity
-- name    : Malliavin.BrownianIteratedConstruction.dense_orderedChainSpan_of_hermiteMultipleIntegralIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:21.081877+00:00
-- url     : https://prove2.me/theorems/69217e85-4d01-5870-9cb7-fe7c752d2f32
-- title:
--   Brownian Iterated Construction: dense ordered Chain Span of hermite Multiple Integral Identity
-- statement:
--   The Hermite/multiple-integral identity makes the ordered Brownian chain span dense.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L79-L86
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermiteMultipleIntegral.lean#L79-L86

import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Definitions.Def_Malliavin_BrownianHermiteMultipleIntegral
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

theorem Malliavin.BrownianIteratedConstruction.dense_orderedChainSpan_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (hgen : IsWienerGenerated B)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    Dense (brownianOrderedChainSpan hB : Set (RandomL2 P)) := by sorry
