-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_lintegral_comp_rep_mul
-- name    : GlobalTheory.RightRegFund.lintegral_comp_rep_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:01.727853+00:00
-- url     : https://prove2.me/theorems/0868f412-b3f7-49d7-b6a7-12d6e6b8387b
-- title:
--   Right Reg Fund: lintegral comp rep mul
-- statement:
--   The Right Reg Fund construction uses the lintegral comp rep mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L87-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L87-L113

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

theorem GlobalTheory.RightRegFund.lintegral_comp_rep_mul (hD : IsFundamentalDomain Γ D μ) (hDm : MeasurableSet D)
    (hr : ∀ y, ∃ γ : Γ, r y = (γ : G) * y ∧ r y ∈ D) (φ : G → ℝ≥0∞) (g : G) :
    ∫⁻ x in D, φ (r (x * g)) ∂μ = ∫⁻ x in D, φ x ∂μ := by sorry
