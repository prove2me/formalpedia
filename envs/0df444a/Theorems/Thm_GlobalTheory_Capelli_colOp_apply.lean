-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_colOp_apply
-- name    : GlobalTheory.Capelli.colOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:07.624197+00:00
-- url     : https://prove2.me/theorems/c4ae283d-a177-459b-a69c-e84970b16ba0
-- title:
--   Capelli: col Op apply
-- statement:
--   The Capelli construction uses the col Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L56-L58

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
variable {I J I' J' : Type*}

theorem GlobalTheory.Capelli.colOp_apply [Fintype I] (z : I × J → σ) (k l : J) (P : MvPolynomial σ K) :
    colOp K z k l P = ∑ a, X (z (a, k)) * pderiv (z (a, l)) P := by sorry
