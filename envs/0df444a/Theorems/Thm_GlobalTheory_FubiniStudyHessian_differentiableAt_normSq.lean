-- Prove2me | Theorems.Thm_GlobalTheory_FubiniStudyHessian_differentiableAt_normSq
-- name    : GlobalTheory.FubiniStudyHessian.differentiableAt_normSq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:25.053799+00:00
-- url     : https://prove2.me/theorems/536c6eac-1c3c-41a0-943b-1d92213c7d0a
-- title:
--   Fubini Study Hessian: differentiable At norm Sq
-- statement:
--   The Fubini Study Hessian construction uses the differentiable At norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexHessianLogOneAddNormSq.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexHessianLogOneAddNormSq.lean#L31-L32

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

theorem GlobalTheory.FubiniStudyHessian.differentiableAt_normSq (x : V n) : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2) x := by sorry
