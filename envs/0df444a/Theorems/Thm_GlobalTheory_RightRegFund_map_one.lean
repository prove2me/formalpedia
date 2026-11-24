-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_map_one
-- name    : GlobalTheory.RightRegFund.map_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:10.381782+00:00
-- url     : https://prove2.me/theorems/31423894-8a26-486b-87e8-877bcd7bbd26
-- title:
--   Right Reg Fund: map one
-- statement:
--   The Right Reg Fund construction uses the map one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L117-L122

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
variable [μ.IsMulRightInvariant]
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}

theorem GlobalTheory.RightRegFund.map_one (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D)
    (hR : ∀ g F, (R g F : G → ℂ) =ᵐ[μ.restrict D] fun x => F (r (x * g))) : R 1 = 1 := by sorry
