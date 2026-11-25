-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_subQuotShortComplex_shortExact
-- name    : GroundTheory.ProfCoh.subQuotShortComplex_shortExact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:24.170198+00:00
-- url     : https://prove2.me/theorems/fd43328c-5d6d-4e81-9404-49c8e872fc97
-- title:
--   Prof Coh: sub Quot Short Complex short Exact
-- statement:
--   The Prof Coh construction uses the sub Quot Short Complex short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L75-L84

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
omit [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.subQuotShortComplex_shortExact (A : Rep.{u} k G) (W : Submodule k A)
    (h : ∀ g, W ≤ W.comap (A.ρ g)) : (subQuotShortComplex A W h).ShortExact := by sorry
