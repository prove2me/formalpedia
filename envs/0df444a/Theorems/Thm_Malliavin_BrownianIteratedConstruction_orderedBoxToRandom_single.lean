-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_orderedBoxToRandom_single
-- name    : Malliavin.BrownianIteratedConstruction.orderedBoxToRandom_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:08.237164+00:00
-- url     : https://prove2.me/theorems/f535a917-5800-5d75-9711-813a799a3451
-- title:
--   Brownian Iterated Construction: ordered Box To Random single
-- statement:
--   The Brownian Iterated Construction construction uses the ordered Box To Random single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L455-L458
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L455-L458

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.orderedBoxToRandom_single (hB : IsPreBrownianReal B P)
    {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToRandom hB n (Finsupp.single a c) = c • chainIntegralLp hB a.u a.v := by sorry
