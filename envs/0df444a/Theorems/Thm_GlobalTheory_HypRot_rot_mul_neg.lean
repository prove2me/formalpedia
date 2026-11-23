-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_rot_mul_neg
-- name    : GlobalTheory.HypRot.rot_mul_neg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:40.954453+00:00
-- url     : https://prove2.me/theorems/3aa6511e-b4c2-4013-bc2a-d06fd48a2388
-- title:
--   Hyp Rot: rot mul neg
-- statement:
--   The Hyp Rot construction uses the rot mul neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L49-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.HypRot
variable {r : ℕ}

theorem GlobalTheory.HypRot.rot_mul_neg {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    rot j k u * rot j k (-u) = 1 := by sorry
