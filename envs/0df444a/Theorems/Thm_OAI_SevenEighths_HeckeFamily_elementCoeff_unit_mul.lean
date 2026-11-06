-- Prove2me | Theorems.Thm_OAI_SevenEighths_HeckeFamily_elementCoeff_unit_mul
-- name    : OAI.SevenEighths.HeckeFamily.elementCoeff_unit_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:39:54.512415+00:00
-- url     : https://prove2.me/theorems/ab253b58-fd1a-4ff5-bdaa-635f59c5ca91
-- title:
--   Hecke Family: element Coeff unit mul
-- statement:
--   The Hecke Family construction uses the element Coeff unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Family.lean#L60-L64
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/Family.lean#L60-L64

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily

theorem OAI.SevenEighths.HeckeFamily.elementCoeff_unit_mul (χ : Character) (u : Oˣ) (z : O) :
    elementCoeff χ ((u : O) * z) = elementCoeff χ z := by sorry
