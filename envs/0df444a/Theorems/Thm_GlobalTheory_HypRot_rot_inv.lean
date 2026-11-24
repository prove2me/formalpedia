-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_rot_inv
-- name    : GlobalTheory.HypRot.rot_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:12:55.824858+00:00
-- url     : https://prove2.me/theorems/a3bf5843-e043-4f04-a19e-e4291e25d3ca
-- title:
--   Hyp Rot: rot inv
-- statement:
--   The Hyp Rot construction uses the rot inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L69-L70

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

theorem GlobalTheory.HypRot.rot_inv {j k : Fin r} (h : j ≠ k) {u : ℂ} (hu : u * star u = 1) :
    (rot j k u)⁻¹ = rot j k (-u) := by sorry
