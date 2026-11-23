-- Prove2me | Theorems.Thm_GlobalTheory_BSP_norm_toDisc_pow_le
-- name    : GlobalTheory.BSP.norm_toDisc_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:31.098889+00:00
-- url     : https://prove2.me/theorems/b76f4440-c18d-464d-8dfa-13ea71a7036a
-- title:
--   BSP: norm to Disc pow le
-- statement:
--   The BSP construction uses the norm to Disc pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L394-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L394-L403

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

theorem GlobalTheory.BSP.norm_toDisc_pow_le (k : ℕ) (hρ : 0 < ρ) :
    ‖_root_.GlobalTheory.BSP.toDisc l u ρ (u ^ k)‖ ≤ (ρ : ℝ) ^ k := by sorry
