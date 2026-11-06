-- Prove2me | Theorems.Thm_OAI_ActualEisensteinSieve_productQuadratic_not_factor_right
-- name    : OAI.ActualEisensteinSieve.productQuadratic_not_factor_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:51:28.723347+00:00
-- url     : https://prove2.me/theorems/8c16dcf9-e0f8-4e79-a3e7-641282a3e55d
-- title:
--   Actual Eisenstein Sieve: product Quadratic not factor right
-- statement:
--   The Actual Eisenstein Sieve construction uses the product Quadratic not factor right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L209-L226
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinIdeals.lean#L209-L226

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

theorem OAI.ActualEisensteinSieve.productQuadratic_not_factor_right
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ P) ≠ 2) :
    ¬ ∃ f : (O ⧸ Q) → ℤ, ∀ x : O,
      localQuadratic P x * localQuadratic Q x = f (Ideal.Quotient.mk Q x) := by sorry
