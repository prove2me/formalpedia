-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitiveOnIdeals_of_field
-- name    : OAI.SevenEighths.FiniteFourier.primitiveOnIdeals_of_field
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:42:18.363167+00:00
-- url     : https://prove2.me/theorems/a42c5463-0a06-478c-9927-c91b1bbf0e57
-- title:
--   Finite Fourier: primitive On Ideals of field
-- statement:
--   The Finite Fourier construction uses the primitive On Ideals of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L30-L35
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L30-L35

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

theorem OAI.SevenEighths.FiniteFourier.primitiveOnIdeals_of_field {F : Type*} [Field F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) : IsPrimitiveOnIdeals χ := by sorry
