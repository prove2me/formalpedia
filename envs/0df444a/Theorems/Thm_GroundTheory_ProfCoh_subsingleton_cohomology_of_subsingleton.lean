-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_subsingleton
-- name    : GroundTheory.ProfCoh.subsingleton_cohomology_of_subsingleton
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:37:40.845909+00:00
-- url     : https://prove2.me/theorems/f367a6ab-256e-4ad4-8b5f-98a7a30dca24
-- title:
--   Prof Coh: subsingleton cohomology of subsingleton
-- statement:
--   The Prof Coh construction uses the subsingleton cohomology of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L51-L55

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
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
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.subsingleton_cohomology_of_subsingleton (A : Rep.{u} k G) [IsDiscreteRep A]
    [Subsingleton A] (n : ℕ) : Subsingleton (cohomology A n) := by sorry
