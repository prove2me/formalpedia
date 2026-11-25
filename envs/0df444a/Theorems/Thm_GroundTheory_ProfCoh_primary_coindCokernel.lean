-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_primary_coindCokernel
-- name    : GroundTheory.ProfCoh.primary_coindCokernel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:36:10.026834+00:00
-- url     : https://prove2.me/theorems/40e2ffea-b035-4072-9081-ec1dab528511
-- title:
--   Prof Coh: primary coind Cokernel
-- statement:
--   The Prof Coh construction uses the primary coind Cokernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L429-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L429-L435

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

theorem GroundTheory.ProfCoh.primary_coindCokernel [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A]
    {p : ℕ} (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (x : coindCokernel A) :
    ∃ k : ℕ, p ^ k • x = 0 := by sorry
