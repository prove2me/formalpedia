-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_mul_conjugate
-- name    : OAI.SevenEighths.FiniteFourier.primitive_gaussSum_mul_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:36.075819+00:00
-- url     : https://prove2.me/theorems/54f4c1a1-6e2e-4f6a-8a49-2ec87540d4d2
-- title:
--   Finite Fourier: primitive gauss Sum mul conjugate
-- statement:
--   The Finite Fourier construction uses the primitive gauss Sum mul conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L113-L128
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L113-L128

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

theorem OAI.SevenEighths.FiniteFourier.primitive_gaussSum_mul_conjugate (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by sorry
