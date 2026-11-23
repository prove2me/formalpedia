-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_finset_sum
-- name    : GroundTheory.Global.Elliptic.rectIntegral_finset_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:15.578602+00:00
-- url     : https://prove2.me/theorems/d4e528a9-807e-4cf4-ba01-d532e74bc36c
-- title:
--   Elliptic: rect Integral finset sum
-- statement:
--   The Elliptic construction uses the rect Integral finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L132-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/RectangleIntegral.lean#L132-L142

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
variable {z w : ℂ} {f g : ℂ → E}

theorem GroundTheory.Global.Elliptic.rectIntegral_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (hf : ∀ i ∈ s, ContinuousOn (f i) (rectBoundary z w)) :
    rectIntegral (fun u ↦ ∑ i ∈ s, f i u) z w = ∑ i ∈ s, rectIntegral (f i) z w := by sorry
