-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_gI
-- name    : GlobalTheory.HeckeTwo.HDecay.hasDerivAt_gI
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:32.477065+00:00
-- url     : https://prove2.me/theorems/c7b16b30-4447-4ab6-9ae5-7257b8884db2
-- title:
--   HDecay: has Deriv At g I
-- statement:
--   The HDecay construction uses the has Deriv At g I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L87-L91

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

theorem GlobalTheory.HeckeTwo.HDecay.hasDerivAt_gI (hy : y ≠ 0) (t : ℝ) : HasDerivAt (gI y) (-(gI y t) ^ 2) t := by sorry
