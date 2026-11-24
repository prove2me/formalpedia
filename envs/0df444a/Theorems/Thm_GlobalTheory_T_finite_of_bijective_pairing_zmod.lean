-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_of_bijective_pairing_zmod
-- name    : GlobalTheory.T.finite_of_bijective_pairing_zmod
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:39:46.967933+00:00
-- url     : https://prove2.me/theorems/5a909d9c-c20f-4bac-b348-e563ba9d4ff1
-- title:
--   T: finite of bijective pairing zmod
-- statement:
--   The T construction uses the finite of bijective pairing zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmodStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteOfPerfectPairingZmodStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteOfPerfectPairingZmodStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Function
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_of_bijective_pairing_zmod : ∀ (n : ℕ) [NeZero n] (A B C : Type) [AddCommGroup A] [Module (ZMod n) A] [AddCommGroup B] [Module (ZMod n) B] [AddCommGroup C] [Module (ZMod n) C] [Finite C] (b : A →ₗ[ZMod n] B →ₗ[ZMod n] C), Nonempty (C ≃ₗ[ZMod n] ZMod n) → Bijective b → Bijective b.flip → Finite A ∧ Finite B := by sorry
