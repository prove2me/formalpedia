-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_perfect_pairing_zmod
-- name    : GlobalTheory.finite_of_perfect_pairing_zmod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:14.771509+00:00
-- url     : https://prove2.me/theorems/4b547491-e7a5-4ecf-9272-904d348b5374
-- title:
--   Global Theory: finite of perfect pairing zmod
-- statement:
--   The Global Theory construction uses the finite of perfect pairing zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L117-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmod.lean#L117-L151

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

theorem GlobalTheory.finite_of_perfect_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A]
    [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C]
    [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C),
    Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by sorry
