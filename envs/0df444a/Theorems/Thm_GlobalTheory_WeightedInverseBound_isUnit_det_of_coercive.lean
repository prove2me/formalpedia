-- Prove2me | Theorems.Thm_GlobalTheory_WeightedInverseBound_isUnit_det_of_coercive
-- name    : GlobalTheory.WeightedInverseBound.isUnit_det_of_coercive
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:21.551876+00:00
-- url     : https://prove2.me/theorems/f14ff484-55d6-457c-b769-9834ffffaee6
-- title:
--   Weighted Inverse Bound: is Unit det of coercive
-- statement:
--   The Weighted Inverse Bound construction uses the is Unit det of coercive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L74-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeightedLeastSquaresBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
open GlobalTheory
open GlobalTheory.WeightedInverseBound

theorem GlobalTheory.WeightedInverseBound.isUnit_det_of_coercive {g : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y.mulVec x) : IsUnit Y.det := by sorry
