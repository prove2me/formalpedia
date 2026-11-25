-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_cdp_le_iff_forall_simple
-- name    : GroundTheory.ProfCoh.cdp_le_iff_forall_simple
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:44.473007+00:00
-- url     : https://prove2.me/theorems/4efcf85b-a820-4e6b-ba58-bac5c34734e8
-- title:
--   Prof Coh: cdp le iff forall simple
-- statement:
--   The Prof Coh construction uses the cdp le iff forall simple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L474-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L474-L485

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
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem GroundTheory.ProfCoh.cdp_le_iff_forall_simple {p : ℕ} (hp : p.Prime) (n : ℕ) :
    cdp p G ≤ n ↔ ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A],
      IsSimpleOrder (Subrepresentation A.ρ) → (∀ a : A, p • a = 0) →
        Subsingleton (cohomology A (n + 1)) := by sorry
