-- Prove2me | Theorems.Thm_GlobalTheory_CubeFace_differentiableOn_prod
-- name    : GlobalTheory.CubeFace.differentiableOn_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:42.368667+00:00
-- url     : https://prove2.me/theorems/7f729fd4-d78d-4768-9f8b-2667811d4f1f
-- title:
--   Cube Face: differentiable On prod
-- statement:
--   The Cube Face construction uses the differentiable On prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L48-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace

theorem GlobalTheory.CubeFace.differentiableOn_prod {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (s : Finset α) (f : α → E → ℂ) (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun y => ∏ i ∈ s, f i y) U := by sorry
