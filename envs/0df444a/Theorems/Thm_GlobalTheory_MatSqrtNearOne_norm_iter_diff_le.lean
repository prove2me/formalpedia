-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_iter_diff_le
-- name    : GlobalTheory.MatSqrtNearOne.norm_iter_diff_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:34.384171+00:00
-- url     : https://prove2.me/theorems/763fba59-a903-45a1-8963-e0873744f60a
-- title:
--   Mat Sqrt Near One: norm iter diff le
-- statement:
--   The Mat Sqrt Near One construction uses the norm iter diff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L53-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.MatSqrtNearOne
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}

theorem GlobalTheory.MatSqrtNearOne.norm_iter_diff_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) :
    ∀ k, ‖iter u (k + 1) - iter u k‖ ≤ ‖u‖ * ‖u‖ ^ k
  := by sorry
