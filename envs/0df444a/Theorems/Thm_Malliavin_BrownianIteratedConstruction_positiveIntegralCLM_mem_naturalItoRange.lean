-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_positiveIntegralCLM_mem_naturalItoRange
-- name    : Malliavin.BrownianIteratedConstruction.positiveIntegralCLM_mem_naturalItoRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:29.629624+00:00
-- url     : https://prove2.me/theorems/0209e548-15a2-5134-8b65-2c1a602298f4
-- title:
--   Brownian Iterated Construction: positive Integral CLM mem natural Ito Range
-- statement:
--   Every output of the canonical positive-order Brownian operator is a natural Itô terminal
--   value.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L72-L78
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L72-L78

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

theorem Malliavin.BrownianIteratedConstruction.positiveIntegralCLM_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (n : ℕ) (f : IteratedKernel (n + 1)) :
    positiveIntegralCLM hB n f ∈ naturalItoRange hB hsm hnat := by sorry
