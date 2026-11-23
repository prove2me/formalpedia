-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_pderiv_swap
-- name    : GlobalTheory.Capelli.pderiv_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:49:58.687393+00:00
-- url     : https://prove2.me/theorems/5e5ac298-75e5-40ae-8b0e-1afecc2da56d
-- title:
--   Capelli: pderiv swap
-- statement:
--   The Capelli construction uses the pderiv swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L9-L17

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

theorem GlobalTheory.Capelli.pderiv_swap (u v : σ) (P : MvPolynomial σ K) :
    pderiv u (pderiv v P) = pderiv v (pderiv u P) := by sorry
