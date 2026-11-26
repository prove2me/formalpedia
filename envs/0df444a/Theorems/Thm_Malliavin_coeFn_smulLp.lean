-- Prove2me | Theorems.Thm_Malliavin_coeFn_smulLp
-- name    : Malliavin.coeFn_smulLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:26.415878+00:00
-- url     : https://prove2.me/theorems/8594d2da-0012-5252-8ce2-0707e3997f89
-- title:
--   Malliavin: coe Fn smul Lp
-- statement:
--   The Malliavin construction uses the coe Fn smul Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L231-L235
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L231-L235

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift
set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Malliavin.coeFn_smulLp (e : E) (G : Lp ℝ 2 μ) :
    (smulLp e G : Ω → E) =ᵐ[μ] fun ω ↦ G ω • e := by sorry
