-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_pow_dvd_sub_aeval_trunc
-- name    : GlobalTheory.ChartRing.pow_dvd_sub_aeval_trunc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:20.05628+00:00
-- url     : https://prove2.me/theorems/5148e74a-a0cd-45f1-8525-ece66a57c543
-- title:
--   Chart Ring: pow dvd sub aeval trunc
-- statement:
--   The Chart Ring construction uses the pow dvd sub aeval trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L13-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsAdicCompleteComapConstantCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open GlobalTheory GlobalTheory.ChartRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem GlobalTheory.ChartRing.pow_dvd_sub_aeval_trunc (φ : A⟦X⟧ →ₐ[A] S) (n : ℕ) (f : A⟦X⟧) :
    φ X ^ n ∣ φ f - Polynomial.aeval (φ X) (trunc n f) := by sorry
