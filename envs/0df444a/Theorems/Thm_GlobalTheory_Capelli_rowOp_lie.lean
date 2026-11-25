-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_rowOp_lie
-- name    : GlobalTheory.Capelli.rowOp_lie
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:16.164052+00:00
-- url     : https://prove2.me/theorems/b9e1ec57-d72e-446c-be10-0fe2de6f865b
-- title:
--   Capelli: row Op lie
-- statement:
--   The Capelli construction uses the row Op lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L89-L93

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

theorem GlobalTheory.Capelli.rowOp_lie [Fintype J] [DecidableEq I] (z : I × J → σ) (hz : Function.Injective z)
    (i j k l : I) :
    rowOp K z i j * rowOp K z k l - rowOp K z k l * rowOp K z i j =
      (if j = k then rowOp K z i l else 0) - (if l = i then rowOp K z k j else 0) := by sorry
