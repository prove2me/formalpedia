-- Prove2me | Theorems.Thm_GlobalTheory_mk_lt_mk_addMonoidHom_zmod
-- name    : GlobalTheory.mk_lt_mk_addMonoidHom_zmod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:06.222792+00:00
-- url     : https://prove2.me/theorems/c8f0189b-f09b-4bb2-81e5-ae4e84a413a7
-- title:
--   Global Theory: mk lt mk add Monoid Hom zmod
-- statement:
--   The Global Theory construction uses the mk lt mk add Monoid Hom zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L58-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L58-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function Cardinal
open GlobalTheory

theorem GlobalTheory.mk_lt_mk_addMonoidHom_zmod (n : ℕ) : ∀ (A : Type) [AddCommGroup A],
    (∀ x : A, n • x = 0) → n ≠ 0 → Infinite A → #A < #(A →+ ZMod n) := by sorry
