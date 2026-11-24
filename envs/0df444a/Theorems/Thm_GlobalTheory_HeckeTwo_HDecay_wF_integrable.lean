-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_wF_integrable
-- name    : GlobalTheory.HeckeTwo.HDecay.wF_integrable
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:05:31.510064+00:00
-- url     : https://prove2.me/theorems/fe4456f9-6293-4bed-813c-2b69b49695f9
-- title:
--   HDecay: w F integrable
-- statement:
--   The HDecay construction uses the w F integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L203-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L203-L254

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
variable {σ y}

theorem GlobalTheory.HeckeTwo.HDecay.wF_integrable (hy : y ≠ 0) (hσ : 0 < σ.re) (a b : ℕ) : Integrable (wF σ y a b) := by sorry
