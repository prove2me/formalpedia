-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_add_of_primary
-- name    : GroundTheory.ProfCoh.subsingleton_cohomology_add_of_primary
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:40.415886+00:00
-- url     : https://prove2.me/theorems/3bff4d4d-de2a-4815-aee6-d631e48e11dc
-- title:
--   Prof Coh: subsingleton cohomology add of primary
-- statement:
--   The Prof Coh construction uses the subsingleton cohomology add of primary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L437-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L437-L449

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

theorem GroundTheory.ProfCoh.subsingleton_cohomology_add_of_primary [CompactSpace G] {p : ℕ} {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      Subsingleton (cohomology A (m + 1))) (j : ℕ) :
    ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      Subsingleton (cohomology A (m + 1 + j)) := by sorry
