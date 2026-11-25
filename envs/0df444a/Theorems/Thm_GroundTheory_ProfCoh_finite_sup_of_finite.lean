-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_finite_sup_of_finite
-- name    : GroundTheory.ProfCoh.finite_sup_of_finite
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:48.857047+00:00
-- url     : https://prove2.me/theorems/5df64547-5422-5fb6-9056-903740456abc
-- title:
--   Prof Coh: finite sup of finite
-- statement:
--   The Prof Coh construction uses the finite sup of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L349-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L349-L355

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
omit [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.finite_sup_of_finite {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (W₁ W₂ : Submodule R M) [Finite W₁] [Finite W₂] : Finite ↥(W₁ ⊔ W₂) := by sorry
