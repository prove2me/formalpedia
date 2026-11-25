-- Prove2me | Theorems.Thm_GlobalTheory_BSP_exists_mem_ball
-- name    : GlobalTheory.BSP.exists_mem_ball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:26.999277+00:00
-- url     : https://prove2.me/theorems/b1b9aabc-fd4c-40cb-ab7c-07e86b8e28b9
-- title:
--   BSP: exists mem ball
-- statement:
--   The BSP construction uses the exists mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L54-L61

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

theorem GlobalTheory.BSP.exists_mem_ball (y : PreDisc l u ρ) : ∃ r : ℝ, 0 < r ∧ y ∈ ball l u ρ r := by sorry
