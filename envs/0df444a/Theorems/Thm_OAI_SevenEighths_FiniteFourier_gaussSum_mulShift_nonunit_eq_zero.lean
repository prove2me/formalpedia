-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_gaussSum_mulShift_nonunit_eq_zero
-- name    : OAI.SevenEighths.FiniteFourier.gaussSum_mulShift_nonunit_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:24.890865+00:00
-- url     : https://prove2.me/theorems/4ae813a9-8ba3-49c7-975e-786b6231b953
-- title:
--   Finite Fourier: gauss Sum mul Shift nonunit eq zero
-- statement:
--   The Finite Fourier construction uses the gauss Sum mul Shift nonunit eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L88-L98
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L88-L98

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

theorem OAI.SevenEighths.FiniteFourier.gaussSum_mulShift_nonunit_eq_zero (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ)
    {a : R} (ha : ¬ IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by sorry
