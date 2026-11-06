-- Prove2me | Theorems.Thm_OAI_SevenEighths_CharacterTransport_pullback_mul
-- name    : OAI.SevenEighths.CharacterTransport.pullback_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:34:47.593997+00:00
-- url     : https://prove2.me/theorems/5d849f2d-e4fc-469b-a5f0-59be71cebe45
-- title:
--   Character Transport: pullback mul
-- statement:
--   The Character Transport construction uses the pullback mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CharacterTransport.lean#L33-L37
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CharacterTransport.lean#L33-L37

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

theorem OAI.SevenEighths.CharacterTransport.pullback_mul (e : R ≃+* S) (χ ψ : MulChar S ℂ) :
    pullback e (χ * ψ) = pullback e χ * pullback e ψ := by sorry
