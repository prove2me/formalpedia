-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_bijective_nsmul_quotient_primarySubmodule
-- name    : GroundTheory.ProfCoh.bijective_nsmul_quotient_primarySubmodule
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:14.95982+00:00
-- url     : https://prove2.me/theorems/3bce14d9-ef38-43eb-ac41-619b5f14c8ba
-- title:
--   Prof Coh: bijective nsmul quotient primary Submodule
-- statement:
--   The Prof Coh construction uses the bijective nsmul quotient primary Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L181-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CohomologicalDimension/SubsingletonCohomologyOfPrimaryOfFinite.lean#L181-L222

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
variable {k : Type u} [CommRing k]
omit [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.ProfCoh.bijective_nsmul_quotient_primarySubmodule (A : Rep.{u} k G)
    (hA : IsAddTorsion A) {p : ℕ} (hp : p.Prime) :
    Function.Bijective fun x : A ⧸ primarySubmodule A p => p • x := by sorry
