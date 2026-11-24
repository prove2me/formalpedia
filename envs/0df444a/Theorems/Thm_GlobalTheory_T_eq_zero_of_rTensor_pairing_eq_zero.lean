-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_rTensor_pairing_eq_zero
-- name    : GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:40.834694+00:00
-- url     : https://prove2.me/theorems/351fe6ce-56bf-4e52-a45a-607733f5a5a9
-- title:
--   T: eq zero of r Tensor pairing eq zero
-- statement:
--   The T construction uses the eq zero of r Tensor pairing eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RTensorPairingEqZeroOfFlipInjectiveStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RTensorPairingEqZeroOfFlipInjectiveStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RTensorPairingEqZeroOfFlipInjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RTensorPairingEqZeroOfFlipInjectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by sorry
