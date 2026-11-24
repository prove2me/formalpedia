-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_unramifiedExt_iff_isIntegral_base
-- name    : GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:51:15.312465+00:00
-- url     : https://prove2.me/theorems/7b94b66b-f9aa-42dc-81fa-1a2ee9d53a5d
-- title:
--   T: is Integral unramified Ext iff is Integral base
-- statement:
--   The T construction uses the is Integral unramified Ext iff is Integral base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralUnramifiedExtIffIsIntegralBaseStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralUnramifiedExtIffIsIntegralBaseStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralUnramifiedExtIffIsIntegralBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralUnramifiedExtIffIsIntegralBaseStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (a : B.A), @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by sorry
