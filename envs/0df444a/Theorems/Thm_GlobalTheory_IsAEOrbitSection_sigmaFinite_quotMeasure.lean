-- Prove2me | Theorems.Thm_GlobalTheory_IsAEOrbitSection_sigmaFinite_quotMeasure
-- name    : GlobalTheory.IsAEOrbitSection.sigmaFinite_quotMeasure
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:22.760933+00:00
-- url     : https://prove2.me/theorems/ea50b7e5-69b0-4955-a01b-585c53887f0d
-- title:
--   Is AEOrbit Section: sigma Finite quot Measure
-- statement:
--   The Is AEOrbit Section construction uses the sigma Finite quot Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L411-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L411-L418

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
open GlobalTheory.IsAEOrbitSection
variable {D D' : Set X}

theorem GlobalTheory.IsAEOrbitSection.sigmaFinite_quotMeasure (hD : IsAEOrbitSection G D μ) [SigmaFinite μ] :
    SigmaFinite (quotMeasure G μ) := by sorry
