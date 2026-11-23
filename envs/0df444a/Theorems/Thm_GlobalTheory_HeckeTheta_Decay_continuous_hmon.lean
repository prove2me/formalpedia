-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTheta_Decay_continuous_hmon
-- name    : GlobalTheory.HeckeTheta.Decay.continuous_hmon
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:50.496136+00:00
-- url     : https://prove2.me/theorems/f1cdd64d-770d-433c-8ca4-b055fba03cb8
-- title:
--   Decay: continuous hmon
-- statement:
--   The Decay construction uses the continuous hmon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean#L94-L95

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

theorem GlobalTheory.HeckeTheta.Decay.continuous_hmon (m : ℤ) : Continuous (hmon m) := by sorry
