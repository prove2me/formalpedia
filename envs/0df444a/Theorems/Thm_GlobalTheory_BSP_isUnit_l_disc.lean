-- Prove2me | Theorems.Thm_GlobalTheory_BSP_isUnit_l_disc
-- name    : GlobalTheory.BSP.isUnit_l_disc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:40.890879+00:00
-- url     : https://prove2.me/theorems/d0b6f88b-5c45-4514-87bd-5f0c3df48189
-- title:
--   BSP: is Unit l disc
-- statement:
--   The BSP construction uses the is Unit l disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L177-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L177-L181

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
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)

theorem GlobalTheory.BSP.isUnit_l_disc : IsUnit ((l : ℕ) : _root_.GlobalTheory.BSP.Disc l u ρ) := by sorry
