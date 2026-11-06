-- Prove2me | Theorems.Thm_OAI_PowerExtraction_from_finite_sixth_power_rows_with_constant
-- name    : OAI.PowerExtraction.from_finite_sixth_power_rows_with_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:24:57.097211+00:00
-- url     : https://prove2.me/theorems/b74573f6-5fbf-4813-9dbe-87680b3c979d
-- title:
--   Power Extraction: from finite sixth power rows with constant
-- statement:
--   The Power Extraction construction uses the from finite sixth power rows with constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L107-L135
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticNormalization.lean#L107-L135

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

theorem OAI.PowerExtraction.from_finite_sixth_power_rows_with_constant
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε C : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε) (hC : 1 ≤ C)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ C * D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * C * D ^ ((23 / 24 : ℝ) + ε) := by sorry
