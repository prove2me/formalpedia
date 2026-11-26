-- Prove2me | Theorems.Thm_Malliavin_deriv_exp_sub
-- name    : Malliavin.deriv_exp_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:18.230926+00:00
-- url     : https://prove2.me/theorems/2feb9d15-3069-5bdd-9889-b55922f8a8c3
-- title:
--   Malliavin: deriv exp sub
-- statement:
--   The Malliavin construction uses the deriv exp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L623-L627
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L623-L627

import Definitions.Def_Malliavin_DualDerivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Definitions.Def_Malliavin_CylindricalGrowth
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {g : ℝ → ℝ}

theorem Malliavin.deriv_exp_sub (c : ℝ) : deriv (fun x ↦ Real.exp (x - c)) = fun x ↦ Real.exp (x - c) := by sorry
