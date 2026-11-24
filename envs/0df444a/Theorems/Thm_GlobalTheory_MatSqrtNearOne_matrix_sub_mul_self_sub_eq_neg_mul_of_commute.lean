-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_matrix_sub_mul_self_sub_eq_neg_mul_of_commute
-- name    : GlobalTheory.MatSqrtNearOne.matrix_sub_mul_self_sub_eq_neg_mul_of_commute
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:19:22.021818+00:00
-- url     : https://prove2.me/theorems/f089a025-0cdd-4d01-be26-a15983eecd91
-- title:
--   Mat Sqrt Near One: matrix sub mul self sub eq neg mul of commute
-- statement:
--   The Mat Sqrt Near One construction uses the matrix sub mul self sub eq neg mul of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L48-L51

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

theorem GlobalTheory.MatSqrtNearOne.matrix_sub_mul_self_sub_eq_neg_mul_of_commute (u a b : Matrix (Fin n) (Fin n) K) (h : Commute a b) :
    (u - b * b) - (u - a * a) = -((b - a) * (a + b)) := by sorry
