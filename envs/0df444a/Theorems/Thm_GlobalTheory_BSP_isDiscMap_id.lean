-- Prove2me | Theorems.Thm_GlobalTheory_BSP_isDiscMap_id
-- name    : GlobalTheory.BSP.isDiscMap_id
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:56.370949+00:00
-- url     : https://prove2.me/theorems/843bcdff-7d19-425d-b0b2-037ae8dedce2
-- title:
--   BSP: is Disc Map id
-- statement:
--   The BSP construction uses the is Disc Map id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L193-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L193-L195

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

theorem GlobalTheory.BSP.isDiscMap_id :
    _root_.GlobalTheory.BSP.IsDiscMap (RingHom.id A) (RingHom.id (_root_.GlobalTheory.BSP.Disc l u ρ)) := by sorry
