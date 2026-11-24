-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_invariants_comp_subtype_iff
-- name    : GroundTheory.ProfCoh.mem_invariants_comp_subtype_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:14:45.981282+00:00
-- url     : https://prove2.me/theorems/57152594-e15a-4e3f-8b18-2913a7b93483
-- title:
--   Prof Coh: mem invariants comp subtype iff
-- statement:
--   The Prof Coh construction uses the mem invariants comp subtype iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L280-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L280-L286

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

theorem GroundTheory.ProfCoh.mem_invariants_comp_subtype_iff (A : Rep.{w} k G) (U : Subgroup G) (a : A) :
    a ∈ Representation.invariants (A.ρ.comp U.subtype) ↔ U ≤ stabilizer A.ρ a := by sorry
