-- Prove2me | Theorems.Thm_GlobalTheory_exists_measurableSet_orbitSection
-- name    : GlobalTheory.exists_measurableSet_orbitSection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:18.665589+00:00
-- url     : https://prove2.me/theorems/dd9c705e-548d-4ffb-a0e1-cecbb2b64a30
-- title:
--   Global Theory: exists measurable Set orbit Section
-- statement:
--   The Global Theory construction uses the exists measurable Set orbit Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L467-L473
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean#L467-L473

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

theorem GlobalTheory.exists_measurableSet_orbitSection [ProperlyDiscontinuousSMul G X] :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by sorry
