-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_ae_good
-- name    : GlobalTheory.RightRegFund.ae_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:44.645254+00:00
-- url     : https://prove2.me/theorems/42c76ac4-78ef-4973-bddf-7a1f63fa9fc2
-- title:
--   Right Reg Fund: ae good
-- statement:
--   The Right Reg Fund construction uses the ae good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L40-L50

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

theorem GlobalTheory.RightRegFund.ae_good (hD : IsFundamentalDomain Γ D μ) : ∀ᵐ y ∂μ, Good Γ D y := by sorry
