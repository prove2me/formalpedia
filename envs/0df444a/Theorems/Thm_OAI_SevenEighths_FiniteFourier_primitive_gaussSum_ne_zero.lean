-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_ne_zero
-- name    : OAI.SevenEighths.FiniteFourier.primitive_gaussSum_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:26.711421+00:00
-- url     : https://prove2.me/theorems/a1b7e083-7c00-4672-8426-f881c0f3e892
-- title:
--   Finite Fourier: primitive gauss Sum ne zero
-- statement:
--   The Finite Fourier construction uses the primitive gauss Sum ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L143-L149
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L143-L149

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

theorem OAI.SevenEighths.FiniteFourier.primitive_gaussSum_ne_zero (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 := by sorry
