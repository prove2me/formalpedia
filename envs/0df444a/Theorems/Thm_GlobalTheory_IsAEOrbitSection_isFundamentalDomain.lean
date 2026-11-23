-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_isFundamentalDomain
-- name    : GlobalTheory.IsAEOrbitSection.isFundamentalDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:18.176928+00:00
-- url     : https://prove2.me/theorems/6372754e-a2f0-47f7-94f1-f1197b047878
-- title:
--   Is AEOrbit Section: is Fundamental Domain
-- statement:
--   The Is AEOrbit Section construction uses the is Fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L248-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L248-L256

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
variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]

theorem GlobalTheory.IsAEOrbitSection.isFundamentalDomain {D : Set X} (hD : IsAEOrbitSection G D μ)
    (hfree : ∀ g : G, g ≠ 1 → μ {x | g • x = x} = 0) : IsFundamentalDomain G D μ := by sorry
