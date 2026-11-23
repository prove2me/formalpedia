-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_polar_apply
-- name    : GlobalTheory.Capelli.polar_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:31.652478+00:00
-- url     : https://prove2.me/theorems/6cf31818-422f-45a3-a369-0c7ea70e54b3
-- title:
--   Capelli: polar apply
-- statement:
--   The Capelli construction uses the polar apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L29-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]

theorem GlobalTheory.Capelli.polar_apply (u v : σ) (P : MvPolynomial σ K) :
    polar K u v P = X u * pderiv v P := by sorry

attribute [defeq] GlobalTheory.Capelli.polar_apply
