-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_nsmul_cohomology_eq_zero
-- name    : GroundTheory.ProfCoh.nsmul_cohomology_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:47:29.558368+00:00
-- url     : https://prove2.me/theorems/8d7c4b52-aef0-42d4-b805-ce86fe4e43cb
-- title:
--   Prof Coh: nsmul cohomology eq zero
-- statement:
--   The Prof Coh construction uses the nsmul cohomology eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L43-L49

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

theorem GroundTheory.ProfCoh.nsmul_cohomology_eq_zero (A : Rep.{u} k G) [IsDiscreteRep A] {m : ℕ}
    (hm : ∀ a : A, m • a = 0) (n : ℕ) (x : cohomology A n) : m • x = 0 := by sorry
