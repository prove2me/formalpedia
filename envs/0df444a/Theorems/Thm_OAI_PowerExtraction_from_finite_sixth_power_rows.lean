-- Prove2me | Theorems.Thm_OAI_PowerExtraction_from_finite_sixth_power_rows
-- name    : OAI.PowerExtraction.from_finite_sixth_power_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:14:51.145075+00:00
-- url     : https://prove2.me/theorems/5ed8e1b0-4b3c-421a-9ee3-05cb465bf029
-- title:
--   Power Extraction: from finite sixth power rows
-- statement:
--   The Power Extraction construction uses the from finite sixth power rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L265-L289
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L265-L289

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
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

theorem OAI.PowerExtraction.from_finite_sixth_power_rows
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * D ^ ((23 / 24 : ℝ) + ε) := by sorry
