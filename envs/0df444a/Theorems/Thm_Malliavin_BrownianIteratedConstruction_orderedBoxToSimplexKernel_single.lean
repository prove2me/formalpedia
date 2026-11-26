-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_orderedBoxToSimplexKernel_single
-- name    : Malliavin.BrownianIteratedConstruction.orderedBoxToSimplexKernel_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:50:13.16909+00:00
-- url     : https://prove2.me/theorems/ce6320e3-b40e-487b-bed5-eeff532e11ca
-- title:
--   Brownian Iterated Construction: ordered Box To Simplex Kernel single
-- statement:
--   The Brownian Iterated Construction construction uses the ordered Box To Simplex Kernel single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L449-L451
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianIterated.lean#L449-L451

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

theorem Malliavin.BrownianIteratedConstruction.orderedBoxToSimplexKernel_single {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToSimplexKernel n (Finsupp.single a c) = c • orderedBoxSimplexKernel a := by sorry
