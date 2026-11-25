-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_IsDiscreteRep_of_forall_exists_mem_invariants
-- name    : GroundTheory.ProfCoh.IsDiscreteRep.of_forall_exists_mem_invariants
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:02.347478+00:00
-- url     : https://prove2.me/theorems/dbc1f78b-8347-495b-8a6e-51749f8fad38
-- title:
--   Is Discrete Rep: of forall exists mem invariants
-- statement:
--   The Is Discrete Rep construction uses the of forall exists mem invariants property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L297-L302
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/DiscreteModules/IsDiscreteRepIffForallExistsOpenNormalSubgroup.lean#L297-L302

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

theorem GroundTheory.ProfCoh.IsDiscreteRep.of_forall_exists_mem_invariants (A : Rep.{w} k G)
    (h : ∀ a : A, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ a ∈ Representation.invariants (A.ρ.comp U.subtype)) :
    IsDiscreteRep A := by sorry
