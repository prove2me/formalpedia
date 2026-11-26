-- Prove2me | Theorems.Thm_Malliavin_constLp_apply
-- name    : Malliavin.constLp_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:15.869812+00:00
-- url     : https://prove2.me/theorems/b7210cbc-7038-5f81-80be-2924916102dd
-- title:
--   Malliavin: const Lp apply
-- statement:
--   The Malliavin construction uses the const Lp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L321-L321
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L321-L321

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_DualDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.constLp_apply (h : Space μ) : constLp μ h = Lp.const 2 μ h := by sorry
