-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_zero_le_centeredPartCLM_ker
-- name    : Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_zero_le_centeredPartCLM_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:33.377397+00:00
-- url     : https://prove2.me/theorems/05decafa-2264-5133-a3e3-dbd6601a9347
-- title:
--   Brownian Iterated Construction: brownian Homogeneous Chaos zero le centered Part CLM ker
-- statement:
--   The zeroth Brownian homogeneous chaos is killed by the centering operator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L126-L145
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianChaos.lean#L126-L145

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
omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W]

theorem Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_zero_le_centeredPartCLM_ker
    (hB : IsPreBrownianReal B P) :
    (brownianHomogeneousChaos hB 0 : Submodule ℝ (RandomL2 P)) ≤
      (centeredPartCLM (P := P)).ker := by sorry
