-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cohomologyMap_nsmul
-- name    : GroundTheory.ProfCoh.cohomologyMap_nsmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:16.958222+00:00
-- url     : https://prove2.me/theorems/bc6f256b-49d5-44d8-a7cd-4f1996487330
-- title:
--   Prof Coh: cohomology Map nsmul
-- statement:
--   The Prof Coh construction uses the cohomology Map nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L32-L36

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

theorem GroundTheory.ProfCoh.cohomologyMap_nsmul {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] (m : ℕ)
    (f : A ⟶ B) (n : ℕ) : cohomologyMap (m • f) n = m • cohomologyMap f n := by sorry
