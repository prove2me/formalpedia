-- Prove2me | Theorems.Thm_GlobalTheory_finrank_range_fderiv_lt_of_volume_image_eq_zero
-- name    : GlobalTheory.finrank_range_fderiv_lt_of_volume_image_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:14.393139+00:00
-- url     : https://prove2.me/theorems/b88c4e09-0eeb-5329-99a2-f2e3e8d77747
-- title:
--   Global Theory: finrank range fderiv lt of volume image eq zero
-- statement:
--   The Global Theory construction uses the finrank range fderiv lt of volume image eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankRangeFderivLtOfVolumeImageEqZero.lean#L6-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankRangeFderivLtOfVolumeImageEqZero.lean#L6-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankRangeFderivLtOfVolumeImageEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open GlobalTheory

theorem GlobalTheory.finrank_range_fderiv_lt_of_volume_image_eq_zero :
    ∀ (n : ℕ) (h : (Fin n → ℂ) → (Fin n → ℂ)) (W : Set (Fin n → ℂ)), IsOpen W → AnalyticOnNhd ℂ h W → volume (h '' W) = 0 → ∀ y ∈ W, Module.finrank ℂ (LinearMap.range (fderiv ℂ h y : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) < n := by sorry
