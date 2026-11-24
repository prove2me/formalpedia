-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_rep_eq
-- name    : GlobalTheory.RightRegFund.rep_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:33.83807+00:00
-- url     : https://prove2.me/theorems/e0c29eb2-3726-43e2-9048-ae446af97109
-- title:
--   Right Reg Fund: rep eq
-- statement:
--   The Right Reg Fund construction uses the rep eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L25-L28

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
variable {Γ : Subgroup G} {D : Set G} {r : G → G}

theorem GlobalTheory.RightRegFund.rep_eq (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    {γ : Γ} (hγ : (γ : G) * y ∈ D) : r y = γ * y := by sorry
