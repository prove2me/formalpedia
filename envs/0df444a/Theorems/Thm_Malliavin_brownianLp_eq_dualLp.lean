-- Prove2me | Theorems.Thm_Malliavin_brownianLp_eq_dualLp
-- name    : Malliavin.brownianLp_eq_dualLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:54.181639+00:00
-- url     : https://prove2.me/theorems/bf64c6ab-bbd3-4717-8a8f-dfb09377ca82
-- title:
--   Malliavin: brownian Lp eq dual Lp
-- statement:
--   The Brownian coordinate `B t` is the class of the functional `L t`.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L270-L274
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L270-L274

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
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [SecondCountableTopology W]

theorem Malliavin.brownianLp_eq_dualLp (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (t : ℝ≥0) : brownianLp hB t = dualLp P (L t) := by sorry
