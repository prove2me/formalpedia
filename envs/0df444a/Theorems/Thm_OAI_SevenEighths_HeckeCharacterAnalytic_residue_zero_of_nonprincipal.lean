-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeCharacterAnalytic_residue_zero_of_nonprincipal
-- name    : OAI.SevenEighths.HeckeCharacterAnalytic.residue_zero_of_nonprincipal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:17:06.315197+00:00
-- url     : https://prove2.me/theorems/bf952170-342b-4c75-aabf-36eeebe0f90a
-- title:
--   Hecke Character Analytic: residue zero of nonprincipal
-- statement:
--   The Hecke Character Analytic construction uses the residue zero of nonprincipal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean#L74-L85
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/CharacterAnalytic.lean#L74-L85

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Coordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_CharacterAnalytic
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeCharacterAnalytic

theorem OAI.SevenEighths.HeckeCharacterAnalytic.residue_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    χ.residue 0 = 0 := by sorry
