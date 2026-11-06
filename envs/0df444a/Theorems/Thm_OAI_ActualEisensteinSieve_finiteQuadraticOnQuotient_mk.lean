-- Prove2me | Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadraticOnQuotient_mk
-- name    : OAI.ActualEisensteinSieve.finiteQuadraticOnQuotient_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:41:55.313847+00:00
-- url     : https://prove2.me/theorems/0a30adf1-41c2-4fb3-b32a-8c12d55c7393
-- title:
--   Actual Eisenstein Sieve: finite Quadratic On Quotient mk
-- statement:
--   The Actual Eisenstein Sieve construction uses the finite Quadratic On Quotient mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L573-L582
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L573-L582

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

theorem OAI.ActualEisensteinSieve.finiteQuadraticOnQuotient_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    finiteQuadraticOnQuotient P
        (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ j : ι, localQuadratic (P j) x := by sorry
