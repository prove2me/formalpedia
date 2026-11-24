-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_invariants_comp_subtype_antitone
-- name    : GroundTheory.ProfCoh.invariants_comp_subtype_antitone
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:36:54.193263+00:00
-- url     : https://prove2.me/theorems/5f4b9818-8c3e-43fb-9daf-fe26ae6da0df
-- title:
--   Prof Coh: invariants comp subtype antitone
-- statement:
--   The Prof Coh construction uses the invariants comp subtype antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L319-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L319-L323

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
omit [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.invariants_comp_subtype_antitone (A : Rep.{w} k G) {U V : Subgroup G} (h : U ≤ V) :
    Representation.invariants (A.ρ.comp V.subtype) ≤ Representation.invariants (A.ρ.comp U.subtype) := by sorry
