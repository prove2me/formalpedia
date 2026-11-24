-- Prove2me | Theorems.Thm_GlobalTheory_RightRegFund_ae_good_mul
-- name    : GlobalTheory.RightRegFund.ae_good_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:36.883842+00:00
-- url     : https://prove2.me/theorems/5a22e875-d4b7-4d0f-bcaa-c2269576f54e
-- title:
--   Right Reg Fund: ae good mul
-- statement:
--   The Right Reg Fund construction uses the ae good mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean#L84-L85

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

theorem GlobalTheory.RightRegFund.ae_good_mul (hD : IsFundamentalDomain Γ D μ) (g : G) : ∀ᵐ y ∂μ, Good Γ D (y * g) := by sorry
