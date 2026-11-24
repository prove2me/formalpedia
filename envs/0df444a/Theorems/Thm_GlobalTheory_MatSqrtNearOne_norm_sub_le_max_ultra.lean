-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_sub_le_max_ultra
-- name    : GlobalTheory.MatSqrtNearOne.norm_sub_le_max_ultra
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:32.430923+00:00
-- url     : https://prove2.me/theorems/de3f661e-4ebc-42f8-a4f9-e0088c24694f
-- title:
--   Mat Sqrt Near One: norm sub le max ultra
-- statement:
--   The Mat Sqrt Near One construction uses the norm sub le max ultra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L26-L28

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

theorem GlobalTheory.MatSqrtNearOne.norm_sub_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A - B‖ ≤ max ‖A‖ ‖B‖ := by sorry
