-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_good_mul_iff
-- name    : GlobalTheory.RightRegFund.good_mul_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:08.926247+00:00
-- url     : https://prove2.me/theorems/ee9698bf-6b0c-4810-acd9-05c8befeab35
-- title:
--   Right Reg Fund: good mul iff
-- statement:
--   The Right Reg Fund construction uses the good mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L19-L21

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

theorem GlobalTheory.RightRegFund.good_mul_iff {Γ : Subgroup G} {D : Set G} {y : G} (δ : Γ) :
    Good Γ D ((δ : G) * y) ↔ Good Γ D y := by sorry
