-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subsingleton_cohomology_of_cdp_le
-- name    : GroundTheory.ProfCoh.subsingleton_cohomology_of_cdp_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:44:12.581306+00:00
-- url     : https://prove2.me/theorems/1b37737e-834f-5fe9-bfc3-866b82d9f0f2
-- title:
--   Prof Coh: subsingleton cohomology of cdp le
-- statement:
--   The Prof Coh construction uses the subsingleton cohomology of cdp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L250-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L250-L255

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

theorem GroundTheory.ProfCoh.subsingleton_cohomology_of_cdp_le {p : ℕ} (hp : p.Prime) {n : ℕ} (h : cdp p G ≤ n)
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (hA : ∀ a : A, p • a = 0) {q : ℕ}
    (hq : n < q) : Subsingleton (cohomology A q) := by sorry
