-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_iter_le
-- name    : GlobalTheory.MatSqrtNearOne.norm_iter_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:45.89879+00:00
-- url     : https://prove2.me/theorems/ee68e0e6-5758-488a-930b-7826eb8d93d8
-- title:
--   Mat Sqrt Near One: norm iter le
-- statement:
--   The Mat Sqrt Near One construction uses the norm iter le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L39-L46

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

theorem GlobalTheory.MatSqrtNearOne.norm_iter_le {u : Matrix (Fin n) (Fin n) K} (hc : ‖u‖ < 1) : ∀ k, ‖iter u k‖ ≤ ‖u‖
  := by sorry
