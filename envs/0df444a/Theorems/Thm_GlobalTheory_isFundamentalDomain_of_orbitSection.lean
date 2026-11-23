-- Prove2me | Theorems.Thm_GlobalTheory_isFundamentalDomain_of_orbitSection
-- name    : GlobalTheory.isFundamentalDomain_of_orbitSection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:13.262163+00:00
-- url     : https://prove2.me/theorems/142ebfde-71e5-4eec-8dcd-4046da010eac
-- title:
--   Global Theory: is Fundamental Domain of orbit Section
-- statement:
--   The Global Theory construction uses the is Fundamental Domain of orbit Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L231-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L231-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}

theorem GlobalTheory.isFundamentalDomain_of_orbitSection {D : Set X} (hD : NullMeasurableSet D μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D) (hu : ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x)
    (hfree : ∀ g : G, g ≠ 1 → μ {x | g • x = x} = 0) : IsFundamentalDomain G D μ := by sorry
