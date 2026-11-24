-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral
-- name    : GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:36:14.916023+00:00
-- url     : https://prove2.me/theorems/34ed74c5-6245-47e9-b227-39b47682950f
-- title:
--   Unit Lemma: kap Sum eq zero and st Sum mul eq zero of not is Integral
-- statement:
--   The Unit Lemma construction uses the kap Sum eq zero and st Sum mul eq zero of not is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KappaSumZeroAndStableSumMulZeroOfNotIntegral.lean#L57-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KappaSumZeroAndStableSumMulZeroOfNotIntegral.lean#L57-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial

theorem GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral :
    ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B₁ B₂ : _root_.GlobalTheory.UnitLemma.InvAlg K),
      ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) →
      _root_.GlobalTheory.UnitLemma.InvAlg.kapSum B₁ B₂ = 0 ∧
        B₁.stSum * B₂.stSum = 0 := by sorry
