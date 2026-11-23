-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_offN_projP
-- name    : GlobalTheory.HypRot.offN_projP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:05.698803+00:00
-- url     : https://prove2.me/theorems/9bdbb8e2-d93f-4953-9d18-ef5422b44ccb
-- title:
--   Hyp Rot: off N proj P
-- statement:
--   The Hyp Rot construction uses the off N proj P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L37-L42

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

theorem GlobalTheory.HypRot.offN_projP {j k : Fin r} (h : j ≠ k) (u : ℂ) :
    offN j k u * projP j k = offN j k u := by sorry
