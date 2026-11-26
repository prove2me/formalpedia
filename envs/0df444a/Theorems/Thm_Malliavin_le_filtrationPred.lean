-- Prove2me | Theorems.Thm_Malliavin_le_filtrationPred
-- name    : Malliavin.le_filtrationPred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:27.717313+00:00
-- url     : https://prove2.me/theorems/38cb8ee7-2735-5aac-a730-2e020c83b1b6
-- title:
--   Malliavin: le filtration Pred
-- statement:
--   The Malliavin construction uses the le filtration Pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L569-L570
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/PointwiseCondExp.lean#L569-L570

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

theorem Malliavin.le_filtrationPred {s t : ℝ≥0} (hst : s < t) : 𝓕 s ≤ filtrationPred 𝓕 t := by sorry
