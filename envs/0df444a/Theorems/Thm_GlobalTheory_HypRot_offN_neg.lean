-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_offN_neg
-- name    : GlobalTheory.HypRot.offN_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:15.491874+00:00
-- url     : https://prove2.me/theorems/5c488a63-9b94-402b-84e0-e8985ce3b421
-- title:
--   Hyp Rot: off N neg
-- statement:
--   The Hyp Rot construction uses the off N neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L20-L21

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

theorem GlobalTheory.HypRot.offN_neg (j k : Fin r) (u : ℂ) : offN j k (-u) = - offN j k u := by sorry
