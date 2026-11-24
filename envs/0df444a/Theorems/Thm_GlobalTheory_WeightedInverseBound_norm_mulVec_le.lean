-- Prove2me | Theorems.Thm_GlobalTheory_WeightedInverseBound_norm_mulVec_le
-- name    : GlobalTheory.WeightedInverseBound.norm_mulVec_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:16.078661+00:00
-- url     : https://prove2.me/theorems/a3ea8543-85c1-4739-a442-aa3020c23c05
-- title:
--   Weighted Inverse Bound: norm mul Vec le
-- statement:
--   The Weighted Inverse Bound construction uses the norm mul Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulInvMulPosSemidefUniformBound.lean#L82-L92

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

theorem GlobalTheory.WeightedInverseBound.norm_mulVec_le {m : Type} [Fintype m] {g : ℕ} {Y : Matrix m (Fin g) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ j k, |Y j k| ≤ C) (z : Fin g → ℝ) :
    ‖Y.mulVec z‖ ≤ g * C * ‖z‖ := by sorry
