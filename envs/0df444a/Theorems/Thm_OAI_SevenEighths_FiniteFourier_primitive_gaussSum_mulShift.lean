-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_mulShift
-- name    : OAI.SevenEighths.FiniteFourier.primitive_gaussSum_mulShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:24.657619+00:00
-- url     : https://prove2.me/theorems/a644f631-7730-44aa-862c-c534ab0b674a
-- title:
--   Finite Fourier: primitive gauss Sum mul Shift
-- statement:
--   The Finite Fourier construction uses the primitive gauss Sum mul Shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L100-L106
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L100-L106

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

theorem OAI.SevenEighths.FiniteFourier.primitive_gaussSum_mulShift (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by sorry
