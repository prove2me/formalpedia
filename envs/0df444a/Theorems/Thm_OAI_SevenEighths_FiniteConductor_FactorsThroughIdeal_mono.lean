-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_FactorsThroughIdeal_mono
-- name    : OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:07.913203+00:00
-- url     : https://prove2.me/theorems/ed9a2921-89a6-491b-b06d-1adb2c2ff1b7
-- title:
--   Factors Through Ideal: mono
-- statement:
--   The Factors Through Ideal construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L81-L84
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/FiniteConductor.lean#L81-L84

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]

theorem OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.mono {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by sorry
