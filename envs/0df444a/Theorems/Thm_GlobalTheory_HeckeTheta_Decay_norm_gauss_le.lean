-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTheta_Decay_norm_gauss_le
-- name    : GlobalTheory.HeckeTheta.Decay.norm_gauss_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:59.038517+00:00
-- url     : https://prove2.me/theorems/870115a7-bf64-4fa4-ba02-7c8605f1bd30
-- title:
--   Decay: norm gauss le
-- statement:
--   The Decay construction uses the norm gauss le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L53-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L53-L61

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

theorem GlobalTheory.HeckeTheta.Decay.norm_gauss_le (n : I → ℤ) (w : I → ℂ) :
    ‖gauss n w‖ ≤ gC n * Real.exp (-Real.pi * ∑ i, ‖w i‖ ^ 2) := by sorry
