-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_colOp_lie
-- name    : GlobalTheory.Capelli.colOp_lie
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:03.624612+00:00
-- url     : https://prove2.me/theorems/035b65c4-044b-4f9e-ab9b-c1d4db198cff
-- title:
--   Capelli: col Op lie
-- statement:
--   The Capelli construction uses the col Op lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L73-L87

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

theorem GlobalTheory.Capelli.colOp_lie [Fintype I] [DecidableEq J] (z : I × J → σ) (hz : Function.Injective z)
    (i j k l : J) :
    colOp K z i j * colOp K z k l - colOp K z k l * colOp K z i j =
      (if j = k then colOp K z i l else 0) - (if l = i then colOp K z k j else 0) := by sorry
