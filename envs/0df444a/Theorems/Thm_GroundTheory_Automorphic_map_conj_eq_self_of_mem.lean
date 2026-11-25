-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_map_conj_eq_self_of_mem
-- name    : GroundTheory.Automorphic.map_conj_eq_self_of_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:00.479814+00:00
-- url     : https://prove2.me/theorems/5acd3a82-b07a-4822-baad-99bfef5b9f63
-- title:
--   Automorphic: map conj eq self of mem
-- statement:
--   The Automorphic construction uses the map conj eq self of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L91-L94

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

theorem GroundTheory.Automorphic.map_conj_eq_self_of_mem (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] {K : Subgroup G}
    (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : μ.map (conjCME k) = μ := by sorry
