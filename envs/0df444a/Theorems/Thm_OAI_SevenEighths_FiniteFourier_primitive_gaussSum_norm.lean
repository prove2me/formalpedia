-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteFourier_primitive_gaussSum_norm
-- name    : OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:00.887348+00:00
-- url     : https://prove2.me/theorems/99a32644-d6e0-4a0f-89db-b803408b90a7
-- title:
--   Finite Fourier: primitive gauss Sum norm
-- statement:
--   The Finite Fourier construction uses the primitive gauss Sum norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L138-L141
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteFourier.lean#L138-L141

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

theorem OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card R : ℝ) := by sorry
