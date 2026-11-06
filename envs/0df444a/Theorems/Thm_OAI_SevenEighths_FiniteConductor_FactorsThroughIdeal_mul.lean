-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_FactorsThroughIdeal_mul
-- name    : OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:13:38.027207+00:00
-- url     : https://prove2.me/theorems/3acf27b3-5e98-435f-806a-90d66b60728d
-- title:
--   Factors Through Ideal: mul
-- statement:
--   The Factors Through Ideal construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L107-L112
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L107-L112

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]

theorem OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.mul {χ ψ : MulChar R ℂ} {I J : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    FactorsThroughIdeal (χ * ψ) (I ⊓ J) := by sorry
