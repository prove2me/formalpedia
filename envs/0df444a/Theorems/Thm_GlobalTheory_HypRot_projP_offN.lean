-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_projP_offN
-- name    : GlobalTheory.HypRot.projP_offN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:04.638802+00:00
-- url     : https://prove2.me/theorems/151de02e-a438-4949-a510-030c099acd34
-- title:
--   Hyp Rot: proj P off N
-- statement:
--   The Hyp Rot construction uses the proj P off N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L31-L35

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

theorem GlobalTheory.HypRot.projP_offN {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    projP j k * offN j k u = offN j k u := by sorry
