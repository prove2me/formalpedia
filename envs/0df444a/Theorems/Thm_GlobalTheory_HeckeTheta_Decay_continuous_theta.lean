-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTheta_Decay_continuous_theta
-- name    : GlobalTheory.HeckeTheta.Decay.continuous_theta
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:06:12.852714+00:00
-- url     : https://prove2.me/theorems/c6495bc5-9d90-4f9e-862f-c016ba066d3e
-- title:
--   Decay: continuous theta
-- statement:
--   The Decay construction uses the continuous theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L97-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L97-L129

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

theorem GlobalTheory.HeckeTheta.Decay.continuous_theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ)
    (ha : ∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) :
    Continuous (theta e a n) := by sorry
