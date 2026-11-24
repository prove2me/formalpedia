-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_rep_mul
-- name    : GlobalTheory.RightRegFund.rep_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:04.290705+00:00
-- url     : https://prove2.me/theorems/c9cb2c45-b36d-4050-a8f1-5aae7669acf9
-- title:
--   Right Reg Fund: rep mul
-- statement:
--   The Right Reg Fund construction uses the rep mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L30-L35

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

theorem GlobalTheory.RightRegFund.rep_mul (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {y : G} (h : Good Γ D y)
    (δ : Γ) : r ((δ : G) * y) = r y := by sorry
