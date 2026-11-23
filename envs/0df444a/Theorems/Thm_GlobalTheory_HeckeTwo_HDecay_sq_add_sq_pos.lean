-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_sq_add_sq_pos
-- name    : GlobalTheory.HeckeTwo.HDecay.sq_add_sq_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:02.417634+00:00
-- url     : https://prove2.me/theorems/26f8711e-6361-40df-a560-1c43380fa00d
-- title:
--   HDecay: sq add sq pos
-- statement:
--   The HDecay construction uses the sq add sq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L83-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {y}

theorem GlobalTheory.HeckeTwo.HDecay.sq_add_sq_pos (hy : y ≠ 0) (t : ℝ) : 0 < t ^ 2 + y ^ 2 := by sorry
