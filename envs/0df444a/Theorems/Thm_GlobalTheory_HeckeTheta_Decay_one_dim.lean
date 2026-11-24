-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTheta_Decay_one_dim
-- name    : GlobalTheory.HeckeTheta.Decay.one_dim
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:09.567444+00:00
-- url     : https://prove2.me/theorems/c84d9064-df93-41b3-81cf-ff0ffb6545d3
-- title:
--   Decay: one dim
-- statement:
--   The Decay construction uses the one dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L131-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L131-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]

theorem GlobalTheory.HeckeTheta.Decay.one_dim {σ c R t : ℝ} (hc : 0 < c) (hR : 0 ≤ R) (ht : -R ≤ t) :
    σ * t - c * Real.exp t ≤ ((|σ| + 1) ^ 2 / (2 * c) + (|σ| + 1) * R) - |t| := by sorry
