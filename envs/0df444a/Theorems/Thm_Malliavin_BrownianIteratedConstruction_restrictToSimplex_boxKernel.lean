-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_restrictToSimplex_boxKernel
-- name    : Malliavin.BrownianIteratedConstruction.restrictToSimplex_boxKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:52:06.349468+00:00
-- url     : https://prove2.me/theorems/bf6ad75f-013b-442b-8e76-d7c0bc107db4
-- title:
--   Brownian Iterated Construction: restrict To Simplex box Kernel
-- statement:
--   Restricting an ordered-box kernel gives its simplex-space indicator.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L632-L643
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L632-L643

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_BrownianIterated
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
open Malliavin.BrownianIteratedConstruction
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.restrictToSimplex_boxKernel {n : ℕ} (a : OrderedBoxIndex n) :
    restrictToSimplex n (boxKernel a.u a.v) = orderedBoxSimplexKernel a := by sorry
