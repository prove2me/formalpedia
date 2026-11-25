-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_finite_stable_submodule
-- name    : GroundTheory.ProfCoh.exists_finite_stable_submodule
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:22.209937+00:00
-- url     : https://prove2.me/theorems/8e6d1454-2ae3-57cc-8f32-fd490746381e
-- title:
--   Prof Coh: exists finite stable submodule
-- statement:
--   The Prof Coh construction uses the exists finite stable submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L357-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L357-L387

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

theorem GroundTheory.ProfCoh.exists_finite_stable_submodule [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] {p : ℕ} (hp : 0 < p) (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (a : A) :
    ∃ W : Submodule (ULift.{u} ℤ) A, (∀ g, W ≤ W.comap (A.ρ g)) ∧ Finite W ∧ a ∈ W := by sorry
