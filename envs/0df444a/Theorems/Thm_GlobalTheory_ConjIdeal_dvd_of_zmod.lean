-- Prove2me | Theorems.Thm_GlobalTheory_ConjIdeal_dvd_of_zmod
-- name    : GlobalTheory.ConjIdeal.dvd_of_zmod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:25:29.585518+00:00
-- url     : https://prove2.me/theorems/5bd59cda-5845-4207-b785-183b9b80057f
-- title:
--   Conj Ideal: dvd of zmod
-- statement:
--   The Conj Ideal construction uses the dvd of zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsEqNsmulOfForallAddChar.lean#L47-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqNsmulOfForallAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ConjIdeal
variable {O : Type*} [CommRing O]

theorem GlobalTheory.ConjIdeal.dvd_of_zmod (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : Y →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) (y : X) :
    ∃ z : Y, d y = M • z := by sorry
