-- Prove2me | Theorems.Thm_GlobalTheory_BSP_norm_toDisc_le
-- name    : GlobalTheory.BSP.norm_toDisc_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:36.608807+00:00
-- url     : https://prove2.me/theorems/2ba6e73e-0b14-4827-8b0c-87f87ed2cd10
-- title:
--   BSP: norm to Disc le
-- statement:
--   The BSP construction uses the norm to Disc le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L219-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L219-L223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open GlobalTheory GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}

theorem GlobalTheory.BSP.norm_toDisc_le (a : A) :
    ‖_root_.GlobalTheory.BSP.toDisc l u ρ a‖ ≤ 1 := by sorry
