-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_eq_bot_iff
-- name    : GroundTheory.ProfCoh.primaryComponent_eq_bot_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:10.471507+00:00
-- url     : https://prove2.me/theorems/52eaaa42-4ec7-4bdc-93c9-f20eade26ba0
-- title:
--   Prof Coh: primary Component eq bot iff
-- statement:
--   The Prof Coh construction uses the primary Component eq bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L110-L114

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

theorem GroundTheory.ProfCoh.primaryComponent_eq_bot_iff {M : Type*} [AddCommGroup M] {p : ℕ} :
    AddCommGroup.primaryComponent M p = ⊥ ↔ ∀ x : M, (∃ k : ℕ, p ^ k • x = 0) → x = 0 := by sorry
