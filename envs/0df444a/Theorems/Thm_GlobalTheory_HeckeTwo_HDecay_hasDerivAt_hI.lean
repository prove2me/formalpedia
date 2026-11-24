-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_hI
-- name    : GlobalTheory.HeckeTwo.HDecay.hasDerivAt_hI
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:35.419783+00:00
-- url     : https://prove2.me/theorems/a484d261-1cb2-45e6-8d91-b438081a24df
-- title:
--   HDecay: has Deriv At h I
-- statement:
--   The HDecay construction uses the has Deriv At h I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L93-L97

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

theorem GlobalTheory.HeckeTwo.HDecay.hasDerivAt_hI (hy : y ≠ 0) (t : ℝ) : HasDerivAt (hI y) (-(hI y t) ^ 2) t := by sorry
