-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_mul_im_pos_of_sign_mul_pos
-- name    : GlobalTheory.LipschitzTR.mul_im_pos_of_sign_mul_pos
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:03.992025+00:00
-- url     : https://prove2.me/theorems/8bd768c9-9632-494e-801f-cef3d68b0e89
-- title:
--   Lipschitz TR: mul im pos of sign mul pos
-- statement:
--   The Lipschitz TR construction uses the mul im pos of sign mul pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousIsBigORpowLipschitzProductKernel.lean#L12-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousIsBigORpowLipschitzProductKernel.lean#L12-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousIsBigORpowLipschitzProductKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR

theorem GlobalTheory.LipschitzTR.mul_im_pos_of_sign_mul_pos {w : ℂ} {t : ℝ} (h : 0 < (SignType.sign w.im : ℝ) * t) :
    0 < t * w.im := by sorry
