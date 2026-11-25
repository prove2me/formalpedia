-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_primary_of_finite
-- name    : GroundTheory.ProfCoh.subsingleton_cohomology_of_primary_of_finite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:13.175232+00:00
-- url     : https://prove2.me/theorems/9fd6599b-b939-4d21-bce9-24d69876dea6
-- title:
--   Prof Coh: subsingleton cohomology of primary of finite
-- statement:
--   The Prof Coh construction uses the subsingleton cohomology of primary of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L389-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L389-L416

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

theorem GroundTheory.ProfCoh.subsingleton_cohomology_of_primary_of_finite [CompactSpace G] {p : ℕ} (hp : 0 < p) {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Subsingleton (cohomology A m))
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) :
    Subsingleton (cohomology A m) := by sorry
