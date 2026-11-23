-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_add_I_ne
-- name    : GlobalTheory.HeckeTwo.HDecay.add_I_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:52:08.854434+00:00
-- url     : https://prove2.me/theorems/8e2e9929-8c6d-487d-b2aa-4819aa3a0f47
-- title:
--   HDecay: add I ne
-- statement:
--   The HDecay construction uses the add I ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L71-L75

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

theorem GlobalTheory.HeckeTwo.HDecay.add_I_ne (hy : y ≠ 0) (t : ℝ) : (t : ℂ) + (y : ℂ) * I ≠ 0 := by sorry
