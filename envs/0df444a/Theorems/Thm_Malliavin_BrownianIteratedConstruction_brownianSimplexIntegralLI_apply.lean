-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
-- name    : Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:01:41.917222+00:00
-- url     : https://prove2.me/theorems/71e28b1e-dbed-5d71-8216-b62868691f02
-- title:
--   Brownian Iterated Construction: brownian Simplex Integral LI apply
-- statement:
--   The Brownian Iterated Construction construction uses the brownian Simplex Integral LI apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L43-L47
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaosHilbertSum.lean#L43-L47

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

theorem Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    brownianSimplexIntegralLI hB hsm n f = simplexIntegral hB (n + 1) f := by sorry

attribute [defeq] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
