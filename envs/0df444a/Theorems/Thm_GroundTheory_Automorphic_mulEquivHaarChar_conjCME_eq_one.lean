-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mulEquivHaarChar_conjCME_eq_one
-- name    : GroundTheory.Automorphic.mulEquivHaarChar_conjCME_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:31:21.040275+00:00
-- url     : https://prove2.me/theorems/1645c05e-8590-4d31-b0bc-f34ca41525f0
-- title:
--   Automorphic: mul Equiv Haar Char conj CME eq one
-- statement:
--   The Automorphic construction uses the mul Equiv Haar Char conj CME eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L68-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L68-L89

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem GroundTheory.Automorphic.mulEquivHaarChar_conjCME_eq_one {K : Subgroup G} (hK : IsCompact (K : Set G)) {k : G}
    (hk : k ∈ K) : mulEquivHaarChar (conjCME k) = 1 := by sorry
