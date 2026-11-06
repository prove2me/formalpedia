-- Prove2me | Theorems.Thm_OAI_SevenEighths_Parameters_exists_central_budget
-- name    : OAI.SevenEighths.Parameters.exists_central_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:52.228514+00:00
-- url     : https://prove2.me/theorems/265e3f5a-c45b-4be5-b467-21ea1805619f
-- title:
--   Parameters: exists central budget
-- statement:
--   The Parameters construction uses the exists central budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ParametersCentralBudget.lean#L8-L40
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ParametersCentralBudget.lean#L8-L40

import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersDetectorScales
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersCentralBudget
set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.Parameters

theorem OAI.SevenEighths.Parameters.exists_central_budget (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by sorry
