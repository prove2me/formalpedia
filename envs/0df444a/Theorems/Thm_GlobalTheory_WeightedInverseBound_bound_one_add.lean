-- Prove2me | Theorems.Thm_GlobalTheory_WeightedInverseBound_bound_one_add
-- name    : GlobalTheory.WeightedInverseBound.bound_one_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:45.0403+00:00
-- url     : https://prove2.me/theorems/c450a6b4-49de-42c8-b9f7-aeab1e30ebcc
-- title:
--   Weighted Inverse Bound: bound one add
-- statement:
--   The Weighted Inverse Bound construction uses the bound one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L109-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L109-L180

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

theorem GlobalTheory.WeightedInverseBound.bound_one_add {g a : ℕ} (B : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (hB : ∀ i, (B i).PosSemidef) : ∃ K : ℝ, ∀ t : Fin a → ℝ, (∀ i, 0 < t i) → ∀ i x,
      ‖(1 + ∑ l, t l • B l)⁻¹.mulVec ((t i • B i).mulVec x)‖ ≤ K * ‖x‖ := by sorry
