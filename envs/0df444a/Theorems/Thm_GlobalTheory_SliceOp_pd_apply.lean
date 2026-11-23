-- Prove2me | Theorems.Thm_GlobalTheory_SliceOp_pd_apply
-- name    : GlobalTheory.SliceOp.pd_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:09.719845+00:00
-- url     : https://prove2.me/theorems/5b8cb36d-c7b8-4fb0-9d0c-c4917f6f84fb
-- title:
--   Slice Op: pd apply
-- statement:
--   The Slice Op construction uses the pd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClmSupBound.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ClmSupBound.lean#L24-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthElim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ClmSupBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SliceSchwartz
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.SliceOp
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem GlobalTheory.SliceOp.pd_apply {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (w : X) (f : SchwartzMap X ℂ) (x : X) :
    pd w f x = fderiv ℝ f x w := by sorry
