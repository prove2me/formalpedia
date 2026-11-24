-- Prove2me | Theorems.Thm_GlobalTheory_LineCos_lintegral_fsDensity_indicator
-- name    : GlobalTheory.LineCos.lintegral_fsDensity_indicator
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:07:59.905016+00:00
-- url     : https://prove2.me/theorems/5ea67704-94cd-408a-ba1b-5d1f883478eb
-- title:
--   Line Cos: lintegral fs Density indicator
-- statement:
--   The Line Cos construction uses the lintegral fs Density indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalDensityBoundNearPoint.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalDensityBoundNearPoint.lean#L100-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos

theorem GlobalTheory.LineCos.lintegral_fsDensity_indicator (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {A : Set ℝ}
    (hA : MeasurableSet A) :
    ∫⁻ x, (cosSq s G ⁻¹' A).indicator (fun x => ENNReal.ofReal (fsDensity s G x)) x =
      volume.restrict (Icc (0 : ℝ) 1) A := by sorry
