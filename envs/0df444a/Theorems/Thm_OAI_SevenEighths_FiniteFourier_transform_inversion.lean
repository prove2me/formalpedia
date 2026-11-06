-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_transform_inversion
-- name    : OAI.SevenEighths.FiniteFourier.transform_inversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:18.352074+00:00
-- url     : https://prove2.me/theorems/e94a5745-bb76-4a32-a662-3daf0b5032ca
-- title:
--   Finite Fourier: transform inversion
-- statement:
--   The Finite Fourier construction uses the transform inversion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L40-L60
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L40-L60

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

theorem OAI.SevenEighths.FiniteFourier.transform_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (x : R) :
    (∑ a : R, transform ψ f a * ψ (-(a * x))) =
      (Fintype.card R : ℂ) * f x := by sorry
