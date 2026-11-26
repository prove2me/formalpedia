-- Prove2me | Theorems.Thm_Malliavin_hasDerivAt_cutoff
-- name    : Malliavin.hasDerivAt_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:24:45.314378+00:00
-- url     : https://prove2.me/theorems/631930f2-21bb-4206-880c-610359c3d9d9
-- title:
--   Malliavin: has Deriv At cutoff
-- statement:
--   The Malliavin construction uses the has Deriv At cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L79-L84
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/DualDerivative.lean#L79-L84

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

theorem Malliavin.hasDerivAt_cutoff (n : ℕ) (x : ℝ) :
    HasDerivAt (cutoff n) (1 / (1 + (x / (n + 1)) ^ 2)) x := by sorry
