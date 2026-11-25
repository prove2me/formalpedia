-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_primaryComponent_cohomology_eq_bot_of_bijective
-- name    : GroundTheory.ProfCoh.primaryComponent_cohomology_eq_bot_of_bijective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:35:54.573393+00:00
-- url     : https://prove2.me/theorems/7732b360-7c64-568e-8f9c-cb8d1b8229da
-- title:
--   Prof Coh: primary Component cohomology eq bot of bijective
-- statement:
--   The Prof Coh construction uses the primary Component cohomology eq bot of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L131-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L131-L146

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

theorem GroundTheory.ProfCoh.primaryComponent_cohomology_eq_bot_of_bijective (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] {p : ℕ} (hp : Function.Bijective fun a : A => p • a) (n : ℕ) :
    AddCommGroup.primaryComponent (cohomology A n) p = ⊥ := by sorry
