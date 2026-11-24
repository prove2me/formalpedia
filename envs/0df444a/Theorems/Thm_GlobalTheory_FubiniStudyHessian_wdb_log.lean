-- Prove2me | Theorems.Thm_GlobalTheory_FubiniStudyHessian_wdb_log
-- name    : GlobalTheory.FubiniStudyHessian.wdb_log
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:12.454744+00:00
-- url     : https://prove2.me/theorems/52b6e995-5bb1-4fd9-8e1a-6adb003f60dd
-- title:
--   Fubini Study Hessian: wdb log
-- statement:
--   The Fubini Study Hessian construction uses the wdb log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexHessianLogOneAddNormSq.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexHessianLogOneAddNormSq.lean#L50-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexHessianLogOneAddNormSq
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
open GlobalTheory GlobalTheory.FubiniStudyHessian
open ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate
variable {n : ℕ}

theorem GlobalTheory.FubiniStudyHessian.wdb_log (l : Fin n) :
    wdb n l (fun w : V n => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) =
      fun w => (((1 + ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * w l := by sorry
