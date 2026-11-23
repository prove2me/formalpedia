-- Prove2me | Theorems.Thm_GlobalTheory_MatSqrtNearOne_commute_iter
-- name    : GlobalTheory.MatSqrtNearOne.commute_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:18.879695+00:00
-- url     : https://prove2.me/theorems/c46a2621-6769-4a7e-a51c-ccddbfb32e3f
-- title:
--   Mat Sqrt Near One: commute iter
-- statement:
--   The Mat Sqrt Near One construction uses the commute iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametric.lean#L34-L37

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

theorem GlobalTheory.MatSqrtNearOne.commute_iter {u a : Matrix (Fin n) (Fin n) K} (h : Commute a u) :
    ∀ k, Commute a (iter u k)
  := by sorry
