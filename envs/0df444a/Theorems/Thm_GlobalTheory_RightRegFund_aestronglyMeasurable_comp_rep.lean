-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_aestronglyMeasurable_comp_rep
-- name    : GlobalTheory.RightRegFund.aestronglyMeasurable_comp_rep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:59:53.812654+00:00
-- url     : https://prove2.me/theorems/674e6ff3-668b-4b8c-ac84-ea6c0cebf07b
-- title:
--   Right Reg Fund: aestrongly Measurable comp rep
-- statement:
--   The Right Reg Fund construction uses the aestrongly Measurable comp rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L62-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L62-L75

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
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]

theorem GlobalTheory.RightRegFund.aestronglyMeasurable_comp_rep (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) {f : G → ℂ} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable (fun y => f (r y)) μ := by sorry
