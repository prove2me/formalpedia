-- Prove2me | Theorems.Thm_GlobalTheory_PadicLte_norm_pow_prime_sub_one
-- name    : GlobalTheory.PadicLte.norm_pow_prime_sub_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:39:49.82586+00:00
-- url     : https://prove2.me/theorems/9a10ab84-5086-4828-aafb-d8acefe34ab5
-- title:
--   Padic Lte: norm pow prime sub one
-- statement:
--   The Padic Lte construction uses the norm pow prime sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowPrimePowSubOne.lean#L5-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormPowPrimePowSubOne.lean#L5-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowPrimePowSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PadicLte

theorem GlobalTheory.PadicLte.norm_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (u : ℤ_[l])
    (h : ‖u - 1‖ < ‖((l : ℕ) : ℤ_[l])‖) :
    ‖u ^ l - 1‖ = ‖u - 1‖ * ‖((l : ℕ) : ℤ_[l])‖ := by sorry
