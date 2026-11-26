-- Prove2me | Theorems.Thm_Malliavin_abs_cutoff_le
-- name    : Malliavin.abs_cutoff_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:29.794798+00:00
-- url     : https://prove2.me/theorems/c58e1a7e-a98b-4e92-ad5e-12991a14e8bb
-- title:
--   Malliavin: abs cutoff le
-- statement:
--   The Malliavin construction uses the abs cutoff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L64-L71
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L64-L71

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

theorem Malliavin.abs_cutoff_le (n : ℕ) (x : ℝ) : |cutoff n x| ≤ |x| := by sorry
