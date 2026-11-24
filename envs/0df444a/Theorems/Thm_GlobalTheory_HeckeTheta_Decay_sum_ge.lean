-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTheta_Decay_sum_ge
-- name    : GlobalTheory.HeckeTheta.Decay.sum_ge
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:03.788395+00:00
-- url     : https://prove2.me/theorems/a34046c7-eb12-4a45-a548-5602c9344445
-- title:
--   Decay: sum ge
-- statement:
--   The Decay construction uses the sum ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L71-L82

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

theorem GlobalTheory.HeckeTheta.Decay.sum_ge (y : I → ℝ) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (hy : ∀ i, τ ≤ Real.exp (y i)) :
    τ * ‖v‖ ^ 2 ≤ ∑ i, Real.exp (y i) * ‖v i‖ ^ 2 := by sorry
