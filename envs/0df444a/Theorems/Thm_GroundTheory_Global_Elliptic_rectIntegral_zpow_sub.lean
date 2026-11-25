-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_zpow_sub
-- name    : GroundTheory.Global.Elliptic.rectIntegral_zpow_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:38.536354+00:00
-- url     : https://prove2.me/theorems/d161e814-fdfa-4c0a-b8a7-5b8f553820ad
-- title:
--   Elliptic: rect Integral zpow sub
-- statement:
--   The Elliptic construction uses the rect Integral zpow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L197-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L197-L211

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {z w : ℂ}

theorem GroundTheory.Global.Elliptic.rectIntegral_zpow_sub {p : ℂ} {n : ℤ} (hn : n ≠ -1) (hp : p ∉ rectBoundary z w) :
    rectIntegral (fun u ↦ (u - p) ^ n) z w = 0 := by sorry
