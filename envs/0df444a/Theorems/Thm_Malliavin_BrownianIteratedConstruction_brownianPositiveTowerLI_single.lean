-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
-- name    : Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:41.742057+00:00
-- url     : https://prove2.me/theorems/1a83922f-911f-5ddb-b25e-36b3f2f59109
-- title:
--   Brownian Iterated Construction: brownian Positive Tower LI single
-- statement:
--   The Brownian Iterated Construction construction uses the brownian Positive Tower LI single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L70-L76
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L70-L76

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum
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

theorem Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    brownianPositiveTowerLI hB hsm (lp.single 2 n f) =
      simplexIntegral hB (n + 1) f := by sorry
