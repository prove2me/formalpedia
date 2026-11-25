-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_bound_mulEquivHaarChar_conjCME
-- name    : GroundTheory.Automorphic.exists_bound_mulEquivHaarChar_conjCME
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:07:30.722216+00:00
-- url     : https://prove2.me/theorems/e07f347b-453e-4a71-a5e7-3a7bccacc73a
-- title:
--   Automorphic: exists bound mul Equiv Haar Char conj CME
-- statement:
--   The Automorphic construction uses the exists bound mul Equiv Haar Char conj CME property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L47-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L47-L66

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

theorem GroundTheory.Automorphic.exists_bound_mulEquivHaarChar_conjCME {K : Set G} (hK : IsCompact K)
    (hKinv : ∀ k ∈ K, k⁻¹ ∈ K) :
    ∃ B : ℝ≥0, ∀ k ∈ K, mulEquivHaarChar (conjCME k) ≤ B := by sorry
