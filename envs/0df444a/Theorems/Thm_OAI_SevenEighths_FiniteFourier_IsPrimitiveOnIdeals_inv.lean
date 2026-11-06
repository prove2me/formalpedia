-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_IsPrimitiveOnIdeals_inv
-- name    : OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals.inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:26.568467+00:00
-- url     : https://prove2.me/theorems/78129c42-158b-4d87-ae12-f0f9b270411f
-- title:
--   Is Primitive On Ideals: inv
-- statement:
--   The Is Primitive On Ideals construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L21-L28
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L21-L28

import Mathlib.NumberTheory.GaussSum
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ByContra
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
set_option autoImplicit false
open OAI
open scoped BigOperators
open OAI.SevenEighths OAI.SevenEighths.FiniteFourier
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R]

theorem OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals.inv {χ : MulChar R ℂ} (hχ : IsPrimitiveOnIdeals χ) :
    IsPrimitiveOnIdeals χ⁻¹ := by sorry
