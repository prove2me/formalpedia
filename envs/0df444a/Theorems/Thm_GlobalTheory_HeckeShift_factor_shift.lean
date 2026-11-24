-- Prove2me | Theorems.Thm_GlobalTheory_HeckeShift_factor_shift
-- name    : GlobalTheory.HeckeShift.factor_shift
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:22.639794+00:00
-- url     : https://prove2.me/theorems/ffbefe24-cb30-47ab-9d97-c8048dc74b29
-- title:
--   Hecke Shift: factor shift
-- statement:
--   The Hecke Shift construction uses the factor shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeMellinGaussIntegrandUnitMul.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeMellinGaussIntegrandUnitMul.lean#L21-L38

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMul
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
open GlobalTheory GlobalTheory.HeckeShift

theorem GlobalTheory.HeckeShift.factor_shift (n : ℤ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * (z * w)) *
                 Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * (z * w)‖ ^ 2 : ℝ) : ℂ) =
      (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) *
        (GlobalTheory.HeckeTheta.hmon n ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) *
          Complex.exp ((-2 * Real.pi * ‖(Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w‖ ^ 2 : ℝ) : ℂ)) := by sorry
