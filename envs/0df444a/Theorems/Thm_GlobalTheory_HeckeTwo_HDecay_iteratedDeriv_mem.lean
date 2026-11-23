-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_iteratedDeriv_mem
-- name    : GlobalTheory.HeckeTwo.HDecay.iteratedDeriv_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:38.272377+00:00
-- url     : https://prove2.me/theorems/a12bf504-6c9e-4624-9341-405b7861e3d9
-- title:
--   HDecay: iterated Deriv mem
-- statement:
--   The HDecay construction uses the iterated Deriv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L191-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierTransformRapidDecay.lean#L191-L198

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

theorem GlobalTheory.HeckeTwo.HDecay.iteratedDeriv_mem (hy : y ≠ 0) (n : ℕ) : iteratedDeriv n (wF σ y 0 0) ∈ wSpan σ y := by sorry
