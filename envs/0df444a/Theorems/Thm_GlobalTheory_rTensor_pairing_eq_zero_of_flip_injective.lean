-- Prove2me | Theorems.Thm_GlobalTheory_rTensor_pairing_eq_zero_of_flip_injective
-- name    : GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:15:00.742697+00:00
-- url     : https://prove2.me/theorems/cdba4e1a-2ead-424f-8368-2174b2366db7
-- title:
--   Global Theory: r Tensor pairing eq zero of flip injective
-- statement:
--   The Global Theory construction uses the r Tensor pairing eq zero of flip injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RTensorPairingEqZeroOfFlipInjective.lean#L6-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RTensorPairingEqZeroOfFlipInjective.lean#L6-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RTensorPairingEqZeroOfFlipInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory

theorem GlobalTheory.rTensor_pairing_eq_zero_of_flip_injective : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by sorry
