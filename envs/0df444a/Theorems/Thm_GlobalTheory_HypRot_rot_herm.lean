-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_rot_herm
-- name    : GlobalTheory.HypRot.rot_herm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:08.335089+00:00
-- url     : https://prove2.me/theorems/ee142426-cc75-4291-9718-467be0347db9
-- title:
--   Hyp Rot: rot herm
-- statement:
--   The Hyp Rot construction uses the rot herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L75-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L75-L82

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

theorem GlobalTheory.HypRot.rot_herm (j k : Fin r) (u : ℂ) : (rot j k u).IsHermitian := by sorry
