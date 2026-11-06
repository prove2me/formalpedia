-- Prove2me | Theorems.Thm_OAI_ActualEisensteinSieve_finiteQuadratic_not_factor_subproduct
-- name    : OAI.ActualEisensteinSieve.finiteQuadratic_not_factor_subproduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:23.413446+00:00
-- url     : https://prove2.me/theorems/101c229f-18aa-4192-a73a-99c3f401d703
-- title:
--   Actual Eisenstein Sieve: finite Quadratic not factor subproduct
-- statement:
--   The Actual Eisenstein Sieve construction uses the finite Quadratic not factor subproduct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L584-L627
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L584-L627

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

theorem OAI.ActualEisensteinSieve.finiteQuadratic_not_factor_subproduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ s.prod P) → ℤ,
      ∀ x : O,
        finiteQuadraticOnQuotient P
            (Ideal.Quotient.mk (Finset.univ.prod P) x) =
          f (Ideal.Quotient.mk (s.prod P) x) := by sorry
