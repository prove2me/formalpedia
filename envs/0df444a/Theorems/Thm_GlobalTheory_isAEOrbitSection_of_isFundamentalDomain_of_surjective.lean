-- Prove2me | Theorems.Thm_GlobalTheory_isAEOrbitSection_of_isFundamentalDomain_of_surjective
-- name    : GlobalTheory.isAEOrbitSection_of_isFundamentalDomain_of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:08.225971+00:00
-- url     : https://prove2.me/theorems/43bd9cc7-6b84-451d-9bf3-f053a483136b
-- title:
--   Global Theory: is AEOrbit Section of is Fundamental Domain of surjective
-- statement:
--   The Global Theory construction uses the is AEOrbit Section of is Fundamental Domain of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L220-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L220-L227

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

theorem GlobalTheory.isAEOrbitSection_of_isFundamentalDomain_of_surjective [Countable G] {Q : Type*} [Group Q]
    [MulAction Q X] (φ : G →* Q) (hφ : Function.Surjective φ) (hact : ∀ g (x : X), φ g • x = g • x)
    {D : Set X} (hD : IsFundamentalDomain Q D μ) : IsAEOrbitSection G D μ := by sorry
