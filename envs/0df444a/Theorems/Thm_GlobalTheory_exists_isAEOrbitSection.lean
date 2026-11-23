-- Prove2me | Theorems.Thm_GlobalTheory_exists_isAEOrbitSection
-- name    : GlobalTheory.exists_isAEOrbitSection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:27.75225+00:00
-- url     : https://prove2.me/theorems/b0e5c41d-077f-45fa-9ed3-aa7f5b7f6a2a
-- title:
--   Global Theory: exists is AEOrbit Section
-- statement:
--   The Global Theory construction uses the exists is AEOrbit Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L492-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L492-L495

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
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
variable {X}

theorem GlobalTheory.exists_isAEOrbitSection [ProperlyDiscontinuousSMul G X] (μ : Measure X) :
    ∃ D : Set X, MeasurableSet D ∧ IsAEOrbitSection G D μ := by sorry
