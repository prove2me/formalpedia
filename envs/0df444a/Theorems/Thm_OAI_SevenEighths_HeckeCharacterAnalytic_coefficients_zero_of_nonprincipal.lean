-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_coefficients_zero_of_nonprincipal
-- name    : OAI.SevenEighths.HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:16:54.999199+00:00
-- url     : https://prove2.me/theorems/caeb5fde-64f6-4b1e-be53-cc14cedb66dc
-- title:
--   Hecke Character Analytic: coefficients zero of nonprincipal
-- statement:
--   The Hecke Character Analytic construction uses the coefficients zero of nonprincipal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean#L87-L91
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean#L87-L91

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic

theorem OAI.SevenEighths.HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    HeckeFamily.coefficients χ (0, 0) = 0 := by sorry
