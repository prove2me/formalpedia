-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_coefficients_sum_eq_zero
-- name    : OAI.SevenEighths.HeckeCharacterAnalytic.coefficients_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:49.726201+00:00
-- url     : https://prove2.me/theorems/82161e07-5ffa-44a4-9287-2c270ffbb38c
-- title:
--   Hecke Character Analytic: coefficients sum eq zero
-- statement:
--   The Hecke Character Analytic construction uses the coefficients sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean#L48-L66
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean#L48-L66

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic

theorem OAI.SevenEighths.HeckeCharacterAnalytic.coefficients_sum_eq_zero (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    (∑ a, HeckeFamily.coefficients χ a) = 0 := by sorry
