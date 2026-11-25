-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_primarySubmodule_le_comap
-- name    : GroundTheory.ProfCoh.primarySubmodule_le_comap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:53.923636+00:00
-- url     : https://prove2.me/theorems/75f26a81-40a2-47ac-ac1e-13754a2d84fb
-- title:
--   Prof Coh: primary Submodule le comap
-- statement:
--   The Prof Coh construction uses the primary Submodule le comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L175-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L175-L177

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
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {k : Type u} [CommRing k]
omit [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.primarySubmodule_le_comap (A : Rep.{u} k G) (p : ℕ) (g : G) :
    primarySubmodule A p ≤ (primarySubmodule A p).comap (A.ρ g) := by sorry
