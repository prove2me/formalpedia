-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_mul_le_ultra
-- name    : GlobalTheory.MatSqrtNearOne.norm_mul_le_ultra
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:54.856933+00:00
-- url     : https://prove2.me/theorems/cdd34220-a7a0-4cfb-9a7f-0933aa786fee
-- title:
--   Mat Sqrt Near One: norm mul le ultra
-- statement:
--   The Mat Sqrt Near One construction uses the norm mul le ultra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L10-L17

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

theorem GlobalTheory.MatSqrtNearOne.norm_mul_le_ultra (A B : Matrix (Fin n) (Fin n) K) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by sorry
