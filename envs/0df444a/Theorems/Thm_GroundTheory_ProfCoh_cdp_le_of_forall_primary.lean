-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cdp_le_of_forall_primary
-- name    : GroundTheory.ProfCoh.cdp_le_of_forall_primary
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:37.263621+00:00
-- url     : https://prove2.me/theorems/ab4d0efa-3c2c-59ef-b31a-b0548a36d050
-- title:
--   Prof Coh: cdp le of forall primary
-- statement:
--   The Prof Coh construction uses the cdp le of forall primary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L226-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L226-L248

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

theorem GroundTheory.ProfCoh.cdp_le_of_forall_primary {p : ℕ} (hp : p.Prime) {n : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A], (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) →
      ∀ q : ℕ, n < q → Subsingleton (cohomology A q)) :
    cdp p G ≤ n := by sorry
