-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_primary_discreteCoind
-- name    : GroundTheory.ProfCoh.primary_discreteCoind
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:06.52198+00:00
-- url     : https://prove2.me/theorems/8ccd1415-8de7-4b37-9c6f-5ef87387d5dd
-- title:
--   Prof Coh: primary discrete Coind
-- statement:
--   The Prof Coh construction uses the primary discrete Coind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L418-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L418-L427

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

theorem GroundTheory.ProfCoh.primary_discreteCoind [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A]
    {p : ℕ} (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (f : discreteCoind (ULift.{u} ℤ) G A) :
    ∃ k : ℕ, p ^ k • f = 0 := by sorry
