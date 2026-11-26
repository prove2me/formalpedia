-- Prove2me | Theorems.Thm_Malliavin_cutoff_contDiff
-- name    : Malliavin.cutoff_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:13:50.704034+00:00
-- url     : https://prove2.me/theorems/c6e95b76-b683-4ecb-a1e6-5475e9c64fd4
-- title:
--   Malliavin: cutoff cont Diff
-- statement:
--   The Malliavin construction uses the cutoff cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L61-L62
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L61-L62

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

theorem Malliavin.cutoff_contDiff (n : ℕ) : ContDiff ℝ 1 (cutoff n) := by sorry
