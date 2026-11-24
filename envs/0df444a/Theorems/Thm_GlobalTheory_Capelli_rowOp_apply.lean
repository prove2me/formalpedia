-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_rowOp_apply
-- name    : GlobalTheory.Capelli.rowOp_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:27.574019+00:00
-- url     : https://prove2.me/theorems/1b4c591e-11b8-425c-bd8d-329362db7ac2
-- title:
--   Capelli: row Op apply
-- statement:
--   The Capelli construction uses the row Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L60-L62

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

theorem GlobalTheory.Capelli.rowOp_apply [Fintype J] (z : I × J → σ) (a b : I) (P : MvPolynomial σ K) :
    rowOp K z a b P = ∑ k, X (z (a, k)) * pderiv (z (b, k)) P := by sorry
