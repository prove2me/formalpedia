-- Prove2me | Theorems.Thm_Malliavin_wienerIntegralEquiv_symm_apply
-- name    : Malliavin.wienerIntegralEquiv_symm_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:28:34.759017+00:00
-- url     : https://prove2.me/theorems/db710a00-238f-58db-9115-75cead476b31
-- title:
--   Malliavin: wiener Integral Equiv symm apply
-- statement:
--   The Malliavin construction uses the wiener Integral Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L141-L147
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/TimeDerivative.lean#L141-L147

import Definitions.Def_Malliavin_WienerIntegral
import Definitions.Def_Malliavin_FubiniLift
import Definitions.Def_Malliavin_MalliavinDerivative
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_TimeDerivative
import Theorems.Thm_Malliavin_range_wienerIntegral

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem Malliavin.wienerIntegralEquiv_symm_apply (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (wienerIntegralEquiv hB).symm ⟨wienerIntegral hB f, by
      rw [← range_wienerIntegral]; exact ⟨f, rfl⟩⟩ = f := by sorry
