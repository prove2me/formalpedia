-- Prove2me | Theorems.Thm_Malliavin_filtrationPred_le
-- name    : Malliavin.filtrationPred_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:05.089357+00:00
-- url     : https://prove2.me/theorems/a6fa536d-5889-562e-aa15-66f62dad9ffa
-- title:
--   Malliavin: filtration Pred le
-- statement:
--   The Malliavin construction uses the filtration Pred le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L564-L565
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L564-L565

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation
import Definitions.Def_Malliavin_PointwiseCondExp
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P]

theorem Malliavin.filtrationPred_le (t : ℝ≥0) : filtrationPred 𝓕 t ≤ ‹MeasurableSpace W› := by sorry
