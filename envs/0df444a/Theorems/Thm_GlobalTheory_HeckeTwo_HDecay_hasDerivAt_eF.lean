-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_eF
-- name    : GlobalTheory.HeckeTwo.HDecay.hasDerivAt_eF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:05:33.435958+00:00
-- url     : https://prove2.me/theorems/5cfe22b0-4e87-4d7f-ad27-93d0e52897a8
-- title:
--   HDecay: has Deriv At e F
-- statement:
--   The HDecay construction uses the has Deriv At e F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L114-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L114-L125

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

theorem GlobalTheory.HeckeTwo.HDecay.hasDerivAt_eF (hy : y ≠ 0) (t : ℝ) :
    HasDerivAt (eF σ y) (-σ * (gI y t + hI y t) * eF σ y t) t := by sorry
