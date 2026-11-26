-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_orderedBoxToIteratedKernel_single
-- name    : Malliavin.BrownianIteratedConstruction.orderedBoxToIteratedKernel_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:31:55.47188+00:00
-- url     : https://prove2.me/theorems/6913257c-8bc9-4c44-83cd-19944f931561
-- title:
--   Brownian Iterated Construction: ordered Box To Iterated Kernel single
-- statement:
--   The Brownian Iterated Construction construction uses the ordered Box To Iterated Kernel single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L39-L41
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianMultipleIntegralBoxSpan.lean#L39-L41

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.BrownianIteratedConstruction.orderedBoxToIteratedKernel_single {n : ℕ} (a : OrderedBoxIndex n) (c : ℝ) :
    orderedBoxToIteratedKernel n (Finsupp.single a c) = c • boxKernel a.u a.v := by sorry
