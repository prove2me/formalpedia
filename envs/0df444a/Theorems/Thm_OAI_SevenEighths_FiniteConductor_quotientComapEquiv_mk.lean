-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_quotientComapEquiv_mk
-- name    : OAI.SevenEighths.FiniteConductor.quotientComapEquiv_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:14.028801+00:00
-- url     : https://prove2.me/theorems/f83a7279-7c0d-4d2e-9c79-f5af2e10fb33
-- title:
--   Finite Conductor: quotient Comap Equiv mk
-- statement:
--   The Finite Conductor construction uses the quotient Comap Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L41-L43
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L41-L43

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
variable {R : Type*} [CommRing R]

theorem OAI.SevenEighths.FiniteConductor.quotientComapEquiv_mk (M : Ideal R) (I : Ideal (R ⧸ M)) (a : R) :
    quotientComapEquiv M I (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk I (Ideal.Quotient.mk M a) := by sorry
