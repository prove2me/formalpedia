-- Prove2me | Theorems.Thm_Malliavin_tensorL_apply
-- name    : Malliavin.tensorL_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:04:19.173982+00:00
-- url     : https://prove2.me/theorems/aa96b7e5-cf5a-59c4-9f6c-88945d3b8384
-- title:
--   Malliavin: tensor L apply
-- statement:
--   The Malliavin construction uses the tensor L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L322-L323
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/FubiniLift.lean#L322-L323

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

theorem Malliavin.tensorL_apply [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    tensorL g G = tensor g G := by sorry
