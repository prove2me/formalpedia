-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_add_le_max_ultra
-- name    : GlobalTheory.MatSqrtNearOne.norm_add_le_max_ultra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:33.647013+00:00
-- url     : https://prove2.me/theorems/4acbffb0-f9db-422f-8a51-bd0f6a87bf7f
-- title:
--   Mat Sqrt Near One: norm add le max ultra
-- statement:
--   The Mat Sqrt Near One construction uses the norm add le max ultra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L19-L24

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

theorem GlobalTheory.MatSqrtNearOne.norm_add_le_max_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A + B‖ ≤ max ‖A‖ ‖B‖ := by sorry
