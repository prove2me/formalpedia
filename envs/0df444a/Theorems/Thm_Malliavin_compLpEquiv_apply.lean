-- Prove2me | Theorems.Thm_Malliavin_compLpEquiv_apply
-- name    : Malliavin.compLpEquiv_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:28:32.565664+00:00
-- url     : https://prove2.me/theorems/98a4cc57-f194-4420-935f-d527c4bbb767
-- title:
--   Malliavin: comp Lp Equiv apply
-- statement:
--   The Malliavin construction uses the comp Lp Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L121-L122
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L121-L122

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem Malliavin.compLpEquiv_apply (e : E ≃ₗᵢ[ℝ] F) (f : Lp E 2 μ) :
    compLpEquiv e f = compLpₗᵢ e.toLinearIsometry f := by sorry
