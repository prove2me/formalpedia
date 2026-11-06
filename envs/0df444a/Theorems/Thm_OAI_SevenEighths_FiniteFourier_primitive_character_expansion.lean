-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_character_expansion
-- name    : OAI.SevenEighths.FiniteFourier.primitive_character_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:01.57699+00:00
-- url     : https://prove2.me/theorems/34691ef0-1cf4-46a4-9947-3a74328d2d2a
-- title:
--   Finite Fourier: primitive character expansion
-- statement:
--   The Finite Fourier construction uses the primitive character expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L151-L156
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L151-L156

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

theorem OAI.SevenEighths.FiniteFourier.primitive_character_expansion (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) :
    χ a = (∑ x : R, χ⁻¹ x * ψ (a * x)) / gaussSum χ⁻¹ ψ := by sorry
