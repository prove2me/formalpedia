-- Prove2me | Theorems.Thm_GlobalTheory_BSP_denseRange_ofPre
-- name    : GlobalTheory.BSP.denseRange_ofPre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:19.178048+00:00
-- url     : https://prove2.me/theorems/7ef531ef-56f5-4d0d-bebc-ef3cc054029e
-- title:
--   BSP: dense Range of Pre
-- statement:
--   The BSP construction uses the dense Range of Pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L170-L172

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

theorem GlobalTheory.BSP.denseRange_ofPre :
    DenseRange (_root_.GlobalTheory.BSP.ofPre l u ρ) := by sorry
