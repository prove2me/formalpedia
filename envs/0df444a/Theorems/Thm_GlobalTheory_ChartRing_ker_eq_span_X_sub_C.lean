-- Prove2me | Theorems.Thm_GlobalTheory_ChartRing_ker_eq_span_X_sub_C
-- name    : GlobalTheory.ChartRing.ker_eq_span_X_sub_C
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:29.029303+00:00
-- url     : https://prove2.me/theorems/d93f6c5a-5fe5-46e6-afd7-dd7af971c77c
-- title:
--   Chart Ring: ker eq span X sub C
-- statement:
--   The Chart Ring construction uses the ker eq span X sub C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L140-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsAdicCompleteComapConstantCoeff.lean#L140-L148

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
variable {A : Type*} [CommRing A]

theorem GlobalTheory.ChartRing.ker_eq_span_X_sub_C (φ : A⟦X⟧ →ₐ[A] A) :
    RingHom.ker φ = Ideal.span {X - C (φ X)} := by sorry
