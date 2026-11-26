-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_simplexIntegral_mem_naturalItoRange_succ
-- name    : Malliavin.BrownianIteratedConstruction.simplexIntegral_mem_naturalItoRange_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:19.3788+00:00
-- url     : https://prove2.me/theorems/390425c4-21d5-40cc-9562-e24e21f995f2
-- title:
--   Brownian Iterated Construction: simplex Integral mem natural Ito Range succ
-- statement:
--   Every completed positive-order simplex integral is a natural Itô terminal value.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L55-L67
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L55-L67

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

theorem Malliavin.BrownianIteratedConstruction.simplexIntegral_mem_naturalItoRange_succ
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) {n : ℕ}
    (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    simplexIntegral hB (n + 1) f ∈ naturalItoRange hB hsm hnat := by sorry
