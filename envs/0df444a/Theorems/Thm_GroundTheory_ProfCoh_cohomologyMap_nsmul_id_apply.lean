-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_nsmul_id_apply
-- name    : GroundTheory.ProfCoh.cohomologyMap_nsmul_id_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:44:17.69245+00:00
-- url     : https://prove2.me/theorems/80693ddf-5002-5134-a74b-f951ababcab2
-- title:
--   Prof Coh: cohomology Map nsmul id apply
-- statement:
--   The Prof Coh construction uses the cohomology Map nsmul id apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L38-L41

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

theorem GroundTheory.ProfCoh.cohomologyMap_nsmul_id_apply (A : Rep.{u} k G) [IsDiscreteRep A] (m : ℕ) (n : ℕ)
    (x : cohomology A n) : (cohomologyMap (m • 𝟙 A) n).hom x = m • x := by sorry
