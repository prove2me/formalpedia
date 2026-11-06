-- Prove2me | Theorems.Thm_OAI_SevenEighths_CharacterTransport_primitive_pullback_iff
-- name    : OAI.SevenEighths.CharacterTransport.primitive_pullback_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:43:25.377966+00:00
-- url     : https://prove2.me/theorems/fbf24c89-0efa-4913-8df6-1d1460fece6a
-- title:
--   Character Transport: primitive pullback iff
-- statement:
--   The Character Transport construction uses the primitive pullback iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CharacterTransport.lean#L62-L67
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CharacterTransport.lean#L62-L67

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CharacterTransport
open SevenEighths.FiniteFourier
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

theorem OAI.SevenEighths.CharacterTransport.primitive_pullback_iff (e : R ≃+* S) (χ : MulChar S ℂ) :
    IsPrimitiveOnIdeals (pullback e χ) ↔ IsPrimitiveOnIdeals χ := by sorry
