-- Prove2me | Theorems.Thm_OAI_ActualEisensteinSieve_correctedQuadraticProduct_not_factor_without_prime
-- name    : OAI.ActualEisensteinSieve.correctedQuadraticProduct_not_factor_without_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:32:45.368105+00:00
-- url     : https://prove2.me/theorems/591a1ab7-4431-4344-9e54-6c58dd212d73
-- title:
--   Actual Eisenstein Sieve: corrected Quadratic Product not factor without prime
-- statement:
--   The Actual Eisenstein Sieve construction uses the corrected Quadratic Product not factor without prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L834-L897
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L834-L897

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

theorem OAI.ActualEisensteinSieve.correctedQuadraticProduct_not_factor_without_prime
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (hcop : IsCoprime lambdaIdeal (Finset.univ.prod P))
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ lambdaIdeal * s.prod P) → ℤ,
      ∀ x : O,
        correctedQuadraticProduct P x =
          f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) x) := by sorry
