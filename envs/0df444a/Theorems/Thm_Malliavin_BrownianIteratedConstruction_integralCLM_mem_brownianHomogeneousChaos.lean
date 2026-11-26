-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_integralCLM_mem_brownianHomogeneousChaos
-- name    : Malliavin.BrownianIteratedConstruction.integralCLM_mem_brownianHomogeneousChaos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:22.890981+00:00
-- url     : https://prove2.me/theorems/fd5f9cdc-f31e-5469-a388-977e34e18af3
-- title:
--   Brownian Iterated Construction: integral CLM mem brownian Homogeneous Chaos
-- statement:
--   Every output of the canonical order-`n` operator belongs to its Brownian homogeneous
--   chaos.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L94-L98
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L94-L98

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.integralCLM_mem_brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (n : ℕ) (f : IteratedKernel n) :
    integralCLM hB n f ∈ brownianHomogeneousChaos hB n := by sorry
