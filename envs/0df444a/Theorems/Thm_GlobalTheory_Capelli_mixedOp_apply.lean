-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_mixedOp_apply
-- name    : GlobalTheory.Capelli.mixedOp_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:10.093062+00:00
-- url     : https://prove2.me/theorems/5d2fa8e0-7070-5bdd-a82a-becf7a0e41d4
-- title:
--   Capelli: mixed Op apply
-- statement:
--   The Capelli construction uses the mixed Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L64-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L64-L68

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

theorem GlobalTheory.Capelli.mixedOp_apply [Fintype I] [Fintype I'] (z : I × J → σ) (y : I' × J → σ) (k l : J)
    (P : MvPolynomial σ K) :
    mixedOp K z y k l P = ∑ a, X (z (a, k)) * pderiv (z (a, l)) P -
      ∑ b, X (y (b, l)) * pderiv (y (b, k)) P := by sorry
