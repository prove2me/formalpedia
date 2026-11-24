-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_iff_forall_exists_openNormalSubgroup
-- name    : GroundTheory.ProfCoh.isDiscreteRep_iff_forall_exists_openNormalSubgroup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:36:56.88039+00:00
-- url     : https://prove2.me/theorems/f1106887-7dbb-432b-8165-57869cc06ba4
-- title:
--   Prof Coh: is Discrete Rep iff forall exists open Normal Subgroup
-- statement:
--   The Prof Coh construction uses the is Discrete Rep iff forall exists open Normal Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L304-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L304-L316

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits Topology
universe w u v
variable {k : Type u} {G : Type v} [CommRing k] [Group G]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.isDiscreteRep_iff_forall_exists_openNormalSubgroup [CompactSpace G] (A : Rep.{w} k G) :
    IsDiscreteRep A ↔
      ∀ a : A, ∃ U : OpenNormalSubgroup G, a ∈ Representation.invariants (A.ρ.comp U.toSubgroup.subtype) := by sorry
