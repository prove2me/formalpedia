-- Prove2me | Theorems.Thm_Malliavin_partition_succ_le_castSucc
-- name    : Malliavin.partition_succ_le_castSucc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:12.189124+00:00
-- url     : https://prove2.me/theorems/042758c0-8714-5c58-ba5d-aac7c93a8960
-- title:
--   Malliavin: partition succ le cast Succ
-- statement:
--   The Malliavin construction uses the partition succ le cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L149-L153
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/IteratedIntegral.lean#L149-L153

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_Simplex
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_Malliavin_IteratedIntegral
set_option autoImplicit false
open Malliavin
open MeasureTheory
open scoped NNReal
universe u_1 u_2 u_3 u_4 u_7 u_8
universe u₁ u₂ u₃ u₄ u₅
variable {Ω : Type*} [MeasureSpace Ω]
variable {W : ℝ≥0 → Ω → ℝ}
omit [MeasureSpace Ω]

theorem Malliavin.partition_succ_le_castSucc {n : ℕ} (P : Partition n) {i j : Fin n} (h : i < j) :
    P.t i.succ ≤ P.t j.castSucc := by sorry
