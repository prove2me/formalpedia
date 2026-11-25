-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_sub_quot
-- name    : GroundTheory.ProfCoh.subsingleton_cohomology_of_sub_quot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:37:02.514132+00:00
-- url     : https://prove2.me/theorems/62baa4c8-291b-40fa-86bc-b847c9669933
-- title:
--   Prof Coh: subsingleton cohomology of sub quot
-- statement:
--   The Prof Coh construction uses the subsingleton cohomology of sub quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L98-L102

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

theorem GroundTheory.ProfCoh.subsingleton_cohomology_of_sub_quot (A : Rep.{u} k G) [IsDiscreteRep A] (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) (n : ℕ)
    (h₁ : Subsingleton (cohomology (A.subrepresentation W h) n))
    (h₃ : Subsingleton (cohomology (A.quotient W h) n)) : Subsingleton (cohomology A n) := by sorry
