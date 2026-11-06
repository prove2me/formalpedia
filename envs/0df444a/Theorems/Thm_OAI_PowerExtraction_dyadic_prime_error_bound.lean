-- Prove2me | Theorems.Thm_OAI_PowerExtraction_dyadic_prime_error_bound
-- name    : OAI.PowerExtraction.dyadic_prime_error_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:24:59.499817+00:00
-- url     : https://prove2.me/theorems/33487abc-4cbb-452e-96dc-32994d08fdb6
-- title:
--   Power Extraction: dyadic prime error bound
-- statement:
--   The Power Extraction construction uses the dyadic prime error bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L202-L236
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L202-L236

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.PowerExtraction

theorem OAI.PowerExtraction.dyadic_prime_error_bound (D N : ℕ) (hD : 1 ≤ D)
    (hN : (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤ (N : ℝ)) :
    ((64 * (D / N + 1) : ℕ) : ℝ) ≤
      192 * (D : ℝ) ^ (49 / 60 : ℝ) := by sorry
