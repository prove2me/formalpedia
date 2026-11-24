-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_rot_unitary
-- name    : GlobalTheory.HypRot.rot_unitary
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:42.678047+00:00
-- url     : https://prove2.me/theorems/f19bdb1b-5f26-45c9-86d6-0d68f3b8ce41
-- title:
--   Hyp Rot: rot unitary
-- statement:
--   The Hyp Rot construction uses the rot unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L102-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L102-L115

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

theorem GlobalTheory.HypRot.rot_unitary {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1)
    (d : Fin r → ℂ) (hd : d j = - d k) :
    (rot j k u)ᵀ * Matrix.diagonal d * (rot j k u).map (starRingEnd ℂ) = Matrix.diagonal d := by sorry
