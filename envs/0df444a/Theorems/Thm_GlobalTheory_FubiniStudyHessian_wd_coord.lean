-- Prove2me | Theorems.Thm_GlobalTheory_FubiniStudyHessian_wd_coord
-- name    : GlobalTheory.FubiniStudyHessian.wd_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:25.160337+00:00
-- url     : https://prove2.me/theorems/b70ba001-504f-472f-ac6f-b5ed2f1c2325
-- title:
--   Fubini Study Hessian: wd coord
-- statement:
--   The Fubini Study Hessian construction uses the wd coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexHessianLogOneAddNormSq.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexHessianLogOneAddNormSq.lean#L17-L24

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

theorem GlobalTheory.FubiniStudyHessian.wd_coord (j i : Fin n) (x : V n) : wd n j (fun w : V n => w i) x = if j = i then 1 else 0 := by sorry
