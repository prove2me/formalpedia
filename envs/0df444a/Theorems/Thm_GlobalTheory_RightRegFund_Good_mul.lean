-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_Good_mul
-- name    : GlobalTheory.RightRegFund.Good.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:03.248881+00:00
-- url     : https://prove2.me/theorems/e03fbf41-a783-4cd7-906f-d4956947e06d
-- title:
--   Good: mul
-- statement:
--   The Good construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L13-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise
open GlobalTheory GlobalTheory.RightRegFund
variable {G : Type} [Group G]

theorem GlobalTheory.RightRegFund.Good.mul {Γ : Subgroup G} {D : Set G} {y : G} (h : Good Γ D y) (δ : Γ) :
    Good Γ D ((δ : G) * y) := by sorry
