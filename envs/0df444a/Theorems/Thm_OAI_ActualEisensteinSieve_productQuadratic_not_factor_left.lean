-- Prove2me | Theorems.Thm_OAI_ActualEisensteinSieve_productQuadratic_not_factor_left
-- name    : OAI.ActualEisensteinSieve.productQuadratic_not_factor_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:32:09.969197+00:00
-- url     : https://prove2.me/theorems/4f25bd9c-24c3-4d2a-8f5e-9571e41380f5
-- title:
--   Actual Eisenstein Sieve: product Quadratic not factor left
-- statement:
--   The Actual Eisenstein Sieve construction uses the product Quadratic not factor left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L228-L239
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L228-L239

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

theorem OAI.ActualEisensteinSieve.productQuadratic_not_factor_left
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ Q) ≠ 2) :
    ¬ ∃ f : (O ⧸ P) → ℤ, ∀ x : O,
      localQuadratic P x * localQuadratic Q x = f (Ideal.Quotient.mk P x) := by sorry
