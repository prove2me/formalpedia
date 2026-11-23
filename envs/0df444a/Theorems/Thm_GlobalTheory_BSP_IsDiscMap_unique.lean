-- Prove2me | Theorems.Thm_GlobalTheory_BSP_IsDiscMap_unique
-- name    : GlobalTheory.BSP.IsDiscMap.unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:19.920871+00:00
-- url     : https://prove2.me/theorems/cf071a44-4f60-4043-be42-44ee0b27ec5a
-- title:
--   Is Disc Map: unique
-- statement:
--   The Is Disc Map construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L352-L388
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L352-L388

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

theorem GlobalTheory.BSP.IsDiscMap.unique {f : A →+* A'}
    {F G : _root_.GlobalTheory.BSP.Disc l u ρ →+* _root_.GlobalTheory.BSP.Disc l u' ρ'}
    (hF : _root_.GlobalTheory.BSP.IsDiscMap f F)
    (hG : _root_.GlobalTheory.BSP.IsDiscMap f G) : F = G := by sorry
