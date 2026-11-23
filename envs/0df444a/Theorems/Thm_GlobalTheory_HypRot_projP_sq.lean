-- Prove2me | Theorems.Thm_GlobalTheory_HypRot_projP_sq
-- name    : GlobalTheory.HypRot.projP_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:20.895797+00:00
-- url     : https://prove2.me/theorems/f18ddbb5-4006-4bd8-b304-6d357e419fdc
-- title:
--   Hyp Rot: proj P sq
-- statement:
--   The Hyp Rot construction uses the proj P sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsFiniteSymmetricIrreducibleRotations.lean#L44-L47

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

theorem GlobalTheory.HypRot.projP_sq {j k : Fin r} (h : j ≠ k) : projP j k * projP j k = projP j k := by sorry
