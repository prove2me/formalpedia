-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_integers_unramifiedInvolutionExt
-- name    : GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:17:25.344897+00:00
-- url     : https://prove2.me/theorems/9e153b69-a851-434b-9b9d-5209cefdf933
-- title:
--   T: is Integral integers unramified Involution Ext
-- statement:
--   The T construction uses the is Integral integers unramified Involution Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExtStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIntegersUnramifiedInvolutionExtStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExtStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by sorry
