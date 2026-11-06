-- Prove2me | Theorems.Thm_OAI_ActualEisensteinSieve_correctedIdealHom_span
-- name    : OAI.ActualEisensteinSieve.correctedIdealHom_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:32:17.834759+00:00
-- url     : https://prove2.me/theorems/e9de5051-1d35-4421-8c5c-066d102e81ef
-- title:
--   Actual Eisenstein Sieve: corrected Ideal Hom span
-- statement:
--   The Actual Eisenstein Sieve construction uses the corrected Ideal Hom span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L480-L485
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L480-L485

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinSieve

theorem OAI.ActualEisensteinSieve.correctedIdealHom_span
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    correctedIdealHom P (Ideal.span {x}) =
      correctedQuadraticProduct P x := by sorry
